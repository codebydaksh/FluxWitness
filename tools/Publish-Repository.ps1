param([string]$Repository = 'https://github.com/codebydaksh/FluxWitness.git')
$ErrorActionPreference = 'Stop'
if (-not (Get-Command git -ErrorAction SilentlyContinue)) { throw 'Git for Windows is required.' }
$root = Split-Path -Parent $PSScriptRoot
$target = Join-Path $env:TEMP ('FluxWitness-upload-' + [Guid]::NewGuid().ToString('N'))
try {
    git clone $Repository $target
    if ($LASTEXITCODE -ne 0) { throw 'Clone failed. Sign in to GitHub using your regular Git credential flow.' }
    Get-ChildItem -LiteralPath $root -Recurse -Force -File | ForEach-Object {
        $relative = $_.FullName.Substring($root.Length).TrimStart('\', '/')
        if ($relative -match '^(tools|\.git)[\/]') { return }
        $destination = Join-Path $target $relative
        $directory = Split-Path -Parent $destination
        if (-not (Test-Path -LiteralPath $directory)) { New-Item -ItemType Directory -Force -Path $directory | Out-Null }
        Copy-Item -LiteralPath $_.FullName -Destination $destination -Force
    }
    Push-Location $target
    try {
        git add -A
        git diff --cached --stat
        git -c user.name='codebydaksh' -c user.email='192202179+codebydaksh@users.noreply.github.com' commit -m 'Add RC2 source, evidence, images and post-RC2 supplements'
        if ($LASTEXITCODE -ne 0) { throw 'Commit failed or no file changes were found.' }
        git push origin HEAD:main
        if ($LASTEXITCODE -ne 0) { throw 'Push failed. Check repository access.' }
        Write-Host 'Upload completed. Review repository before making it public.'
    } finally { Pop-Location }
} finally {
    if (Test-Path -LiteralPath $target) { Remove-Item -LiteralPath $target -Recurse -Force }
}
