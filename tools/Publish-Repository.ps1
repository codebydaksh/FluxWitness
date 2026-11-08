param([string]$Repository = 'https://github.com/codebydaksh/FluxWitness.git')
$ErrorActionPreference = 'Stop'
if (-not (Get-Command git -ErrorAction SilentlyContinue)) { throw 'Install Git for Windows before using this script.' }
$root = Split-Path -Parent $PSScriptRoot
$target = Join-Path $env:TEMP ('FluxWitness-upload-' + [Guid]::NewGuid().ToString('N'))
try {
    git clone $Repository $target
    if ($LASTEXITCODE -ne 0) { throw 'Git clone failed.' }
    Get-ChildItem $root -Force | Where-Object { $_.Name -notin @('.git','tools') } | ForEach-Object {
        Copy-Item $_.FullName (Join-Path $target $_.Name) -Recurse -Force
    }
    Push-Location $target
    try {
        git add -A
        git diff --cached --stat
        git -c user.name='codebydaksh' -c user.email='192202179+codebydaksh@users.noreply.github.com' commit -m 'Publish FluxWitness RC2 evidence and supplements'
        if ($LASTEXITCODE -ne 0) { throw 'Commit failed.' }
        git push origin HEAD:main
        if ($LASTEXITCODE -ne 0) { throw 'Push failed.' }
        Write-Host 'Repository upload completed.'
    } finally { Pop-Location }
} finally { if (Test-Path $target) { Remove-Item $target -Recurse -Force } }
