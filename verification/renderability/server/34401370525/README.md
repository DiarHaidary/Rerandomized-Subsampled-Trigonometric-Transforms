# Official Palomar rendering passed

[Palomar rendering run 34401370525](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34401370525)
completed successfully for source commit
`d98e7f29472bf79e350712f710b5c19be7f8db76` on 9 September 2026.
The actual server report records `status: pass`, `stage: complete`, empty
errors, and rendering completion at **20:36:40 UTC**.

This is the full official Linux pipeline: trusted source preparation,
confined literate build, core-notation audit, HTML generation, sanitization,
selected declaration checks, and artifact hashing. It confirms that the
named-instance compatibility fix resolves the earlier rendering blocker.

- `report.json`: the unedited report downloaded from Palomar's workflow.
- `bundle/`: the complete sanitized HTML artifact, including
  [the rendered Challenge](bundle/Challenge/index.html), its assets,
  `challenge-metadata.json`, and `artifact-manifest.json`.
- `provenance.json`: the public workflow, artifact ID, independently checked
  archive digest, and verification of all 18 file hashes in the bundle manifest.

The artifact's source Challenge SHA-256 is
`2014066db73506991b7fb4402c27ec0b92cf94f9dd28906c9157a01f0df2a690`.
The artifact tree hash is
`441aa89bf85db0c572bbe0b26ceeeea9b7f3d8811f3f8c7cbe918ce19700a22e`.
Official renderer: `ef2fa1eadcb246c2346ddba39b52eaa53d4bb763`;
Verso: `3bdedf29bada13d8103e6c979001c51dcee210c8`.

## Timeline and submission state

The same source passed [Palomar mechanical verification](../../../palomar/34398823705/README.md).
The rendering workflow started at 20:29:44 UTC, its actual build stage began
at 20:32:49, and the render completed at 20:36:40. Thus the build/render stage
took 3 minutes 51 seconds; the workflow also needed environment preparation.
The earlier interval between mechanical success and the rendering request
was separate from this execution time.

The submitter withdrew the submission at 20:30:38, while the workflow was
preparing its environment. The already dispatched rendering workflow still
finished successfully. Its pass does not undo the withdrawal or establish
automated review completion or registration. A new submission is required
to proceed with those later stages.

Subsequent repository edits correct the axiom metadata and document this
evidence. The checked proof, Challenge, Solution, Comparator configuration,
and build inputs are unchanged; their separate source comparison is retained
with the mechanical verification record.
