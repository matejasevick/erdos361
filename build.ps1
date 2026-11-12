# Erdos #361 -- verification build for Windows PowerShell, one Lean process at a time.
# Run by double-clicking RUN_BUILD.cmd, or:  powershell -ExecutionPolicy Bypass -File .\build.ps1
#
# The project is copied to C:\erdos361-build (outside OneDrive) and built there. The previous
# build copy is cleared first, keeping only the downloaded dependencies
# (C:\erdos361-build\.lake\packages: Mathlib and the packages it requires), so every module of
# this project is compiled from source. One log per step is written to the folder
# "erdos361-build-logs" next to this folder, outside the repository.

$ErrorActionPreference = "Continue"
$src  = $PSScriptRoot
$dst  = "C:\erdos361-build"
$logs = Join-Path (Split-Path $src -Parent) "erdos361-build-logs"
New-Item -ItemType Directory -Force -Path $logs | Out-Null

# Clear the previous build copy, keeping only .lake\packages (downloaded dependencies).
if (Test-Path -LiteralPath $dst) {
    Get-ChildItem -LiteralPath $dst -Force | Where-Object { $_.Name -ne ".lake" } |
        Remove-Item -Recurse -Force
    $lake = Join-Path $dst ".lake"
    if (Test-Path -LiteralPath $lake) {
        Get-ChildItem -LiteralPath $lake -Force | Where-Object { $_.Name -ne "packages" } |
            Remove-Item -Recurse -Force
    }
}
New-Item -ItemType Directory -Force -Path $dst | Out-Null
robocopy $src $dst /E /XD .lake /NFL /NDL /NJH /NJS /NP | Out-Null
Set-Location $dst
$env:Path = "$env:USERPROFILE\.elan\bin;$env:Path"

# Machine resources, for diagnosing memory problems
$cs = Get-CimInstance Win32_ComputerSystem
$os = Get-CimInstance Win32_OperatingSystem
@(
  ("Logical processors : {0}" -f $cs.NumberOfLogicalProcessors),
  ("Physical memory GB : {0:N1} total, {1:N1} free" -f ($cs.TotalPhysicalMemory / 1GB), ($os.FreePhysicalMemory / 1MB)),
  ("Commit limit GB    : {0:N1} total, {1:N1} free" -f ($os.TotalVirtualMemorySize / 1MB), ($os.FreeVirtualMemory / 1MB)),
  ("Started            : {0}" -f (Get-Date -Format s))
) | Out-File -Encoding utf8 -FilePath (Join-Path $logs "00_machine.log")

function Step([string]$name, [string]$cmd) {
    $log = Join-Path $logs "$name.log"
    for ($attempt = 1; $attempt -le 3; $attempt++) {
        Write-Host "=== $name (attempt $attempt): $cmd"
        $t0 = Get-Date
        cmd /c "$cmd > `"$log`" 2>&1"
        $code = $LASTEXITCODE
        $secs = [int]((Get-Date) - $t0).TotalSeconds
        Add-Content -Path $log -Value "`n[exit code: $code, $secs s, attempt $attempt]"
        Write-Host "    -> exit $code after $secs s"
        if ($code -eq 0) { return }
        if (-not (Select-String -Path $log -Pattern "failed to read file" -Quiet)) { return }
        Copy-Item $log (Join-Path $logs "$name.attempt$attempt.log") -Force
        Start-Sleep -Seconds 30
    }
}

Step "01_toolchain" "elan toolchain install leanprover/lean4:v4.31.0 & lean --version"
Step "02_cache_get" "lake exe cache get"
$modules = "Erdos361.Statement", "Erdos361.Core", "Erdos361.GoodCore", "Erdos361.Covering",
           "Erdos361.Freiman", "Erdos361.InverseGlue", "Erdos361.InverseMain", "Erdos361.Asymptotics"
$i = 0
foreach ($m in $modules) { $i++; Step ("03_{0}_{1}" -f $i, $m) "lake build $m" }
Step "04_root"            "lake build Erdos361"
Step "05_challenge"       "lake build Challenge"
Step "06_solution"        "lake build Solution"
Step "07_axioms_original" "lake env lean CheckOriginal.lean"
Step "08_axioms_solution" "lake env lean Solution.lean"
Select-String -Path (Join-Path $dst "Erdos361\*.lean"), (Join-Path $dst "Solution.lean") `
    -Pattern "sorry", "native_decide", "^axiom " | Out-File -Encoding utf8 -FilePath (Join-Path $logs "09_hygiene.log")

# sha256 of every file that was built (the copy in C:\erdos361-build, without .lake)
$files = Get-ChildItem -LiteralPath $dst -Force | Where-Object { $_.Name -ne ".lake" } | ForEach-Object {
    if ($_.PSIsContainer) { Get-ChildItem -LiteralPath $_.FullName -Recurse -File } else { $_ } }
$files | Get-FileHash -Algorithm SHA256 | ForEach-Object {
    "{0}  {1}" -f $_.Hash.ToLower(), $_.Path.Substring($dst.Length + 1).Replace('\', '/') } |
    Sort-Object { $_.Substring(66) } | Out-File -Encoding utf8 -FilePath (Join-Path $logs "10_hashes.log")

"ALL STEPS FINISHED $(Get-Date -Format s)" | Out-File -Encoding utf8 -FilePath (Join-Path $logs "99_done.txt")
Write-Host "Done. Logs are in $logs"
