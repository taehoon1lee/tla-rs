<#
.SYNOPSIS
  Loop-engineering driver: runs fresh headless Claude sessions (default model: haiku), one task per
  iteration, and keeps the repository monotonically green.

.DESCRIPTION
  Each iteration:
    1. feeds loop/PROMPT.md to `claude -p --model <Model>` (fresh context every time), cwd = repo root
    2. restores any protected file the agent touched (harness/, loop/PROMPT.md, this script, CLAUDE.md, ...)
    3. auto-commits leftover changes, then runs the full gate:
         python harness/check.py --gate --update-best
       - pass  -> baseline (harness/results/best.json) updated and committed
       - fail  -> the iteration's commits are saved on branch rejected/iter-NNN-*, HEAD is reset to the
                  pre-iteration commit, and loop/LAST_REJECTED.md explains why (next iteration reads it)
    4. stops after -MaxNoProgress iterations without a commit touching crates/, or when loop/STOP exists.

.EXAMPLE
  pwsh -File loop/run-loop.ps1                         # haiku, up to 100 iterations
  pwsh -File loop/run-loop.ps1 -MaxIterations 5 -IterationTimeoutMin 30
  New-Item loop/STOP                                   # graceful stop after the current iteration
#>
[CmdletBinding()]
param(
    [int]$MaxIterations = 100,
    [string]$Model = "haiku",
    [int]$IterationTimeoutMin = 45,
    [int]$MaxNoProgress = 4,
    [double]$MaxBudgetUsdPerIter = 0,
    [switch]$NoGate,
    # Testing only: path to a .ps1 that stands in for the claude agent (driver self-test).
    [string]$Agent = ""
)

$ErrorActionPreference = "Continue"
$Root = Split-Path -Parent $PSScriptRoot
Set-Location $Root
[Environment]::CurrentDirectory = $Root
$env:PATH = "$env:USERPROFILE\.cargo\bin;$env:PATH"
$env:PYTHONUTF8 = "1"
$Logs = Join-Path $Root "loop\logs"
New-Item -ItemType Directory -Force $Logs | Out-Null
$DriverLog = Join-Path $Logs "driver.log"
$PromptFile = Join-Path $Root "loop\PROMPT.md"
$Rejected = Join-Path $Root "loop\LAST_REJECTED.md"
$AgentSettings = Join-Path $Root "loop\haiku-settings.json"

# Paths the agent must never change (restored from the pre-iteration commit if touched).
$Protected = @(
    "harness/golden", "harness/common.py", "harness/check.py", "harness/tlcout.py", "harness/corpus.py",
    "harness/gen_golden.py", "harness/setup.py", "harness/oracle.py", "harness/corpus.json", "harness/quick.txt",
    "harness/SCHEMA.md", "loop/PROMPT.md", "loop/run-loop.ps1", "loop/haiku-settings.json", "CLAUDE.md",
    ".claude/settings.json", ".gitattributes", ".gitignore"
)

function Write-Log([string]$m) {
    $line = "[{0}] {1}" -f (Get-Date -Format "yyyy-MM-dd HH:mm:ss"), $m
    Write-Host $line
    Add-Content -Path $DriverLog -Value $line -Encoding utf8
}

# NOTE: never name this function "Git" - PowerShell is case-insensitive and it would call itself.
function Invoke-Git {
    $out = & git.exe @args 2>$null
    if ($null -eq $out) { return "" }
    return (($out | ForEach-Object { "$_" }) -join "`n").Trim()
}

function Get-Score {
    # history.csv: time,rev,scope,modules,syntax,parse,parse_msg,models,front,init,verdict,trace,perf,rust_s,java_s,regressions
    $h = Join-Path $Root "harness\results\history.csv"
    if (-not (Test-Path $h)) { return "-" }
    $last = Get-Content $h | Where-Object { $_ -match ",full," } | Select-Object -Last 1
    if (-not $last) { return "-" }
    $c = $last.Split(",")
    return "syntax $($c[4])/$($c[3]) parse $($c[5])/$($c[3]) parse_msg $($c[6])/$($c[3]) front $($c[8])/$($c[7]) " +
        "init $($c[9])/$($c[7]) verdict $($c[10])/$($c[7]) trace $($c[11])/$($c[7]) perf $($c[12])/$($c[7]) " +
        "(rust $($c[13])s java $($c[14])s)"
}

# NOTE: pass "--" QUOTED to Invoke-Git: PowerShell swallows a bare -- as its own end-of-parameters marker.
function Restore-Protected([string]$base, [int]$iter) {
    # protected files that differ from $base (committed or not) + new untracked files under protected paths
    $changed = @((Invoke-Git diff --name-only $base "--" @Protected) -split "`n") +
               @((Invoke-Git ls-files --others --exclude-standard "--" @Protected) -split "`n")
    $changed = @($changed | Where-Object { $_ } | Sort-Object -Unique)
    if ($changed.Count -eq 0) { return }
    Write-Log "iter ${iter}: agent touched protected files -> restoring: $($changed -join ' ')"
    foreach ($f in $changed) {
        & git.exe cat-file -e "${base}:$f" 2>$null
        if ($LASTEXITCODE -eq 0) {
            Invoke-Git restore "--source=$base" --staged --worktree "--" $f | Out-Null
        } else {
            Invoke-Git rm -q -f --cached --ignore-unmatch "--" $f | Out-Null
            Remove-Item -Force -ErrorAction SilentlyContinue (Join-Path $Root $f)
        }
    }
    Invoke-Git commit -qm "loop: restore protected files changed in iteration $iter" | Out-Null
}

# ---- preflight -------------------------------------------------------------------------------
& python harness/setup.py
if ($LASTEXITCODE -ne 0) { Write-Log "setup.py failed; aborting"; exit 1 }
if (-not (Invoke-Git rev-parse HEAD)) { Write-Log "not a git repository with commits; aborting"; exit 1 }
if (Invoke-Git status --porcelain) {
    Invoke-Git add -A | Out-Null
    Invoke-Git commit -qm "loop: snapshot before driver start" | Out-Null
}
if (-not (Test-Path "harness\results\best.json") -and -not $NoGate) {
    Write-Log "creating initial baseline"
    & python harness/check.py --update-best | Select-Object -First 14
    Invoke-Git add -A | Out-Null
    Invoke-Git commit -qm "loop: initial baseline" | Out-Null
}
Write-Log "driver start: model=$Model maxIter=$MaxIterations timeout=${IterationTimeoutMin}m root=$Root score: $(Get-Score)"

$noProgress = 0
for ($i = 1; $i -le $MaxIterations; $i++) {
    if (Test-Path (Join-Path $Root "loop\STOP")) { Write-Log "loop/STOP found -> stopping"; break }
    $tag = "{0:D3}" -f $i
    $stamp = Get-Date -Format "yyyyMMdd-HHmmss"
    $out = Join-Path $Logs "iter-$tag-$stamp.jsonl"
    $err = Join-Path $Logs "iter-$tag-$stamp.stderr.txt"
    $before = Invoke-Git rev-parse HEAD
    if (-not $before) { Write-Log "cannot read HEAD; aborting"; break }
    Write-Log "iter ${i}: start (HEAD $($before.Substring(0,8)))"

    if ($Agent) {
        $exe = "pwsh"; $argList = @("-NoProfile", "-File", $Agent)
    } else {
        $exe = "claude"
        # deny rules (protected files) apply only to the loop agent, via loop/haiku-settings.json
        $argList = @("-p", "--model", $Model, "--dangerously-skip-permissions", "--settings", $AgentSettings,
            "--output-format", "stream-json", "--verbose")
        if ($MaxBudgetUsdPerIter -gt 0) { $argList += @("--max-budget-usd", "$MaxBudgetUsdPerIter") }
    }
    $p = Start-Process -FilePath $exe -ArgumentList $argList -WorkingDirectory $Root -RedirectStandardInput $PromptFile `
        -RedirectStandardOutput $out -RedirectStandardError $err -NoNewWindow -PassThru
    if (-not $p.WaitForExit($IterationTimeoutMin * 60 * 1000)) {
        Write-Log "iter ${i}: TIMEOUT after $IterationTimeoutMin min -> killing"
        & taskkill /F /T /PID $p.Id | Out-Null
    }
    # summarize the agent's final message
    $res = Get-Content $out -ErrorAction SilentlyContinue | Where-Object { $_ -match '"type":"result"' } | Select-Object -Last 1
    if ($res) {
        try {
            $r = $res | ConvertFrom-Json
            $txt = ("" + $r.result) -replace "\s+", " "
            if ($txt.Length -gt 300) { $txt = $txt.Substring(0, 300) }
            Write-Log "iter ${i}: agent done turns=$($r.num_turns) cost=`$$($r.total_cost_usd) :: $txt"
        } catch { Write-Log "iter ${i}: could not parse result line" }
    } else { Write-Log "iter ${i}: no result line (see $err)" }

    Restore-Protected $before $i
    # The baseline may only grow through the driver's own gate run below (protects against a weakened best.json).
    if (Invoke-Git diff --name-only $before "--" harness/results/best.json) {
        Invoke-Git restore "--source=$before" --staged --worktree "--" harness/results/best.json | Out-Null
    }
    if (Invoke-Git status --porcelain) {
        Invoke-Git add -A | Out-Null
        Invoke-Git commit -qm "loop: auto-commit leftovers of iteration $i" | Out-Null
    }

    if (-not $NoGate) {
        $gate = & python harness/check.py --gate --update-best 2>&1 | ForEach-Object { "$_" }
        $gateRc = $LASTEXITCODE
        $build = [bool]($gate | Select-String -SimpleMatch "BUILD FAILED")
        if ($gateRc -ne 0 -or $build) {
            $branch = "rejected/iter-$tag-$stamp"
            Invoke-Git branch -f $branch HEAD | Out-Null
            Invoke-Git reset -q --hard $before | Out-Null
            $why = if ($build) { "cargo build failed" } else { "regression vs harness/results/best.json" }
            $body = @("# Last iteration was REJECTED and reverted by the driver",
                "Iteration $i ($stamp). Its commits are kept on branch ``$branch`` (inspect with ``git log $branch`` / ``git diff $before $branch``).",
                "Reason: $why", "", "Gate output (head):", '```') + ($gate | Select-Object -First 60) + @('```',
                "", "Read this, learn from it (see loop/NOTES.md), then ``git rm loop/LAST_REJECTED.md`` in your iteration's commit.")
            Set-Content -Path $Rejected -Value $body -Encoding utf8
            Invoke-Git add loop/LAST_REJECTED.md | Out-Null
            Invoke-Git commit -qm "loop: iteration $i rejected (saved on $branch)" | Out-Null
            Write-Log "iter ${i}: REJECTED ($why, gate rc=$gateRc) -> reset to $($before.Substring(0,8)), saved $branch"
        } else {
            if (Invoke-Git status --porcelain) {
                Invoke-Git add -A | Out-Null
                Invoke-Git commit -qm "loop: baseline after iteration $i" | Out-Null
            }
            Write-Log "iter ${i}: gate OK :: $(Get-Score)"
        }
    }

    $touched = Invoke-Git diff --name-only $before HEAD "--" crates
    if ($touched) { $noProgress = 0 } else { $noProgress++ }
    if ($noProgress -ge $MaxNoProgress) {
        Write-Log "no crates/ progress for $noProgress iterations -> stopping (inspect loop/logs, adjust TASKS.md, restart)"
        break
    }
}
Write-Log "driver end :: $(Get-Score)"
