# Palomar mechanical verification of the corrected source

The actual [Palomar verification run 34398823705](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34398823705)
passed for source commit `d98e7f29472bf79e350712f710b5c19be7f8db76`.
This is a server result for the corrected Challenge, beyond the earlier
successful local and repository CI checks.

The downloaded `mechanical-report.json` is preserved without content edits.
It reports `status: pass`, empty errors and warnings, successful NanoDa and
Lean kernel replay, accepted source provenance, and the matching MIT license.
`provenance.json` identifies the exact public workflow and artifact, whose
downloaded archive digest was checked against GitHub's advertised SHA-256.

The checked Challenge is 89 lines and 4,484 bytes, with SHA-256
`2014066db73506991b7fb4402c27ec0b92cf94f9dd28906c9157a01f0df2a690`.

The status-page observation supplied by the submitter records:

| Event | Time on 9 September 2026 (UTC) |
|---|---|
| Submitted corrected commit | 20:04:13 |
| Mechanical verification success | 20:13:04 |
| Challenge rendering requested | 20:29:35 |
| Submission withdrawn by submitter | 20:30:38 |

The roughly sixteen-minute interval after mechanical success preceded the
rendering request. Withdrawal occurred while the separate rendering workflow
was still preparing its environment. A waiting message is not a failure report;
the renderer's own result must be checked. An advertised recent-review duration
does not include all workflow setup, queueing, verification, and rendering time.
This mechanical report alone establishes neither rendering success, automated
review completion, nor registration.

The separate [official rendering run subsequently passed](../../renderability/server/34401370525/README.md)
at 20:36:40 UTC. Its full report and sanitized HTML artifact are preserved
there. The submission remains withdrawn; no automated review completion or
registration is claimed.

After this checked snapshot, `formalization.yaml` was corrected to list all
three audited standard axioms: `propext`, `Classical.choice`, and `Quot.sound`.
`subsequent-metadata-check.json` records successful validation of that metadata
change against the same pinned official contract. This does not change the
proof's assumptions or the Challenge, Solution, Comparator, or build inputs.
