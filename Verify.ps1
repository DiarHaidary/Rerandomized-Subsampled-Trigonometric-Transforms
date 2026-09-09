$ErrorActionPreference = 'Stop'
$projectRoot = $PSScriptRoot
$logDirectory = Join-Path $projectRoot 'verification'
New-Item -ItemType Directory -Path $logDirectory -Force | Out-Null
Push-Location -LiteralPath $projectRoot
try {
    [ordered]@{
        status = 'running'
        startedAtUtc = [DateTime]::UtcNow.ToString('o')
    } | ConvertTo-Json | Set-Content -LiteralPath (Join-Path $logDirectory 'result.json') -Encoding utf8
    $leanVersion = (& lake env lean --version | Out-String).Trim()
    if ($LASTEXITCODE -ne 0) { throw 'Could not load the pinned Lean toolchain.' }

    & lake build 2>&1 | Tee-Object -FilePath (Join-Path $logDirectory 'build.log')
    if ($LASTEXITCODE -ne 0) { throw 'The complete project build failed.' }

    $auditOutput = & lake env lean Audit.lean 2>&1
    $auditExitCode = $LASTEXITCODE
    $auditText = $auditOutput | Out-String
    $auditText | Set-Content -LiteralPath (Join-Path $logDirectory 'axioms.log') -Encoding utf8
    if ($auditExitCode -ne 0) { throw 'The statement and axiom audit failed to compile.' }

    $auditSource = Get-Content -LiteralPath (Join-Path $projectRoot 'Audit.lean') -Raw
    $expectedResults = @([regex]::Matches($auditSource, '(?m)^#print\s+axioms\s+(\S+)') |
        ForEach-Object { $_.Groups[1].Value })
    if ($expectedResults.Count -lt 9) { throw 'The audit inventory is unexpectedly incomplete.' }
    $axiomMatches = [regex]::Matches($auditText, "'([^']+)' depends on axioms:\s*\[([^\]]*)\]")
    $actualResults = @($axiomMatches | ForEach-Object { $_.Groups[1].Value })
    if ($axiomMatches.Count -ne $expectedResults.Count -or
        @(Compare-Object $expectedResults $actualResults).Count -ne 0) {
        throw 'The audit did not report exactly the results listed in Audit.lean.'
    }
    $allowedAxioms = @('propext', 'Classical.choice', 'Quot.sound')
    foreach ($match in $axiomMatches) {
        foreach ($name in ($match.Groups[2].Value -split ',')) {
            if ($name.Trim() -notin $allowedAxioms) {
                throw ('Unexpected transitive axiom: ' + $name.Trim())
            }
        }
    }

    $sourceFiles = @(
        Get-ChildItem -LiteralPath (Join-Path $projectRoot 'SRHT') -Recurse -File -Filter '*.lean'
        Get-ChildItem -LiteralPath (Join-Path $projectRoot 'vendor/sparse-fock') -Recurse -File -Filter '*.lean'
        Get-Item -LiteralPath 'SRHT.lean', 'Solution.lean', 'Challenge.lean', 'Audit.lean', 'lakefile.lean', 'lean-toolchain', 'lake-manifest.json', 'comparator.json', 'Verify.ps1'
    )
    foreach ($source in $sourceFiles) {
        if ($source.Extension -eq '.lean' -and $source.Name -ne 'Challenge.lean') {
            $content = Get-Content -LiteralPath $source.FullName -Raw
            if ($content -match '\b(sorry|admit)\b|(?m)^\s*(?:private\s+)?axiom\s') {
                throw ('An unfinished proof or custom axiom was found in ' + $source.FullName)
            }
        }
    }
    $hashes = @($sourceFiles | Sort-Object FullName | ForEach-Object {
        [ordered]@{
            path = $_.FullName.Substring($projectRoot.TrimEnd('\', '/').Length + 1).Replace('\', '/')
            sha256 = (Get-FileHash -LiteralPath $_.FullName -Algorithm SHA256).Hash.ToLowerInvariant()
        }
    })
    [ordered]@{
        status = 'passed'
        verifiedAtUtc = [DateTime]::UtcNow.ToString('o')
        leanVersion = $leanVersion
        auditedResults = $axiomMatches.Count
        auditedTheorems = $expectedResults
        verificationKind = 'Lean build and transitive axiom audit; Comparator and NanoDa evidence is separate'
        challengeProofHoles = 'The independently compiled Challenge.lean has the intentional theorem hole required for comparison; it is not imported by Solution or Audit.'
        permittedFoundations = $allowedAxioms
        sourceFileCount = $sourceFiles.Count
        sourceHashes = $hashes
    } | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath (Join-Path $logDirectory 'result.json') -Encoding utf8
    Write-Output ('PASS: complete project, ' + $axiomMatches.Count + ' axiom audits, and source scan.')
}
catch {
    [ordered]@{
        status = 'failed'
        failedAtUtc = [DateTime]::UtcNow.ToString('o')
        error = $_.Exception.Message
    } | ConvertTo-Json | Set-Content -LiteralPath (Join-Path $logDirectory 'result.json') -Encoding utf8
    throw
}
finally {
    Pop-Location
}
