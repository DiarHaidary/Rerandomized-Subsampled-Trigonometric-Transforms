# Palomar layout and verification boundaries

Prepared against the official [submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/e9c8c238f5695b10f75db7175648a1d0195352c1/CONTRIBUTING.md)
and [starter template](https://github.com/PalomarRegistry/PalomarTemplate/tree/128a6c5ce5f48622e69927ccd639cbff401022e8),
inspected on 9 September 2026. Each Palomar submission uses the policy and
verifier active when submitted; this document records the preparation basis
and observed status, not an acceptance decision.

## Latest submission status

**Official mechanical verification and full Challenge rendering passed** for
the latest submitted snapshot `d98e7f29472bf79e350712f710b5c19be7f8db76`.
It was submitted on 9 September 2026 at 20:04:13 UTC. Palomar's official
mechanical run `34398823705` succeeded at 20:13:04 UTC: its artifact reports
`pass`, empty errors and warnings, and acceptance by both NanoDa and Lean
replay. The
[official verification record](../verification/palomar/34398823705/README.md)
preserves that evidence for this exact commit.

The rendering request was recorded at 20:29:35 UTC;
[workflow 34401370525](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34401370525)
started at 20:29:44 UTC. The submitter withdrew the submission at 20:30:38 UTC
during environment setup. The build, sanitation, and hashing stage began at
20:32:49 UTC, and the workflow completed successfully with its artifact
uploaded by 20:36:43 UTC. The
[official rendering record](../verification/renderability/server/34401370525/README.md)
confirms the full Linux pipeline, including the core-notation audit, HTML
generation, and sanitation. The submission remains withdrawn; completed
automated review and registration are not established. The earlier `7686734`
rendering failure concerns the historical source without the fix.

The status page's estimate of about four minutes refers to recent automated
reviews. It is not an end-to-end deadline: queueing, clean tool and dependency
setup, Challenge rendering, and review occur separately. A rendering-in-progress
message alone does not report a failure.

The structured metadata passed the official PalomarSubmission metadata
contract at revision `ef2fa1eadcb246c2346ddba39b52eaa53d4bb763`.
[`verification/metadata-check.json`](../verification/metadata-check.json)
records that result. It checks metadata structure, required fields,
classification, and declared provenance; it does not detect the root license,
perform editorial review, or validate proof terms.

## Mathematical suitability

The intended audience is researchers in randomized numerical linear algebra,
randomized algorithms, and random matrix concentration. The selected theorem
gives the dimension scaling for the explicitly posed rerandomized Walsh
embedding question and exposes the transform and probability law in the
statement. Its research relevance comes from that mathematical content, not
from the size of the Lean development or the use of automation.

The [source-fidelity account](SOURCE_FIDELITY.md) compares the exact source
model, quantifiers, error convention, and confidence dependence. The root
README and metadata should be read together with the Challenge. They must
not present supporting library results as additional Comparator-certified
claims unless a configuration actually selects them.

## Repository contract

| Requirement | Location or check |
|---|---|
| Substantive proof development | `SRHT/` and the included `vendor/sparse-fock/` sources; no thin-wrapper declaration is needed. |
| Small auditable statement | `Challenge.lean`, importing permitted library material only and exposing the actual Walsh/counting definitions. |
| Completed proof of the same declaration | `Solution.lean`, connected to the full proof library. |
| Exact claim selection | `comparator.json`, selecting `RerandomizedSTT.problem_5_6`. |
| Trusted axioms | Comparator permits only `propext`, `Quot.sound`, and `Classical.choice`; `sorryAx` is excluded from Solution proofs. |
| Pinned build environment | `lean-toolchain`, exactly one root Lakefile, and committed `lake-manifest.json`. |
| Public provenance and limitations | `formalization.yaml`, `notes/SOURCE_FIDELITY.md`, the report, and the preserved audit notes. |
| Snapshot license | One root `LICENSE`, MIT, matching `project.license`; vendored attribution is retained separately. |
| Public exact source snapshot | The public GitHub repository plus a full 40-character commit SHA, selected configuration path `comparator.json`. |
| Clean source archive | No submitted compiled artifacts, Git submodules, LFS pointers, or private/unpinned dependencies; total checked-out source below 500 MiB. |

The policy's Challenge limit is 100 KiB and 1,000 lines; more than 32 KiB or
300 lines receives a warning. Its import closure may use Lean core and
canonical Mathlib dependencies (and the other expressly permitted libraries),
but no project-specific proof module. This requirement is why the Challenge
states transparent elementary definitions without importing `SRHT`.

The deliberate theorem hole in Challenge is the specification for the
comparison. It is allowed by Palomar. The Solution and mathematical proof
development must have completed proofs, and Comparator must reject any
dependency on that hole. Source scans distinguish this one specification
surface from proof sources; a blind whole-repository count of `sorry` would
confuse the two roles.

Every manifest Git dependency must have a public credential-free GitHub HTTPS
URL and a full exact revision. Local `.lake` caches and Windows junctions are
not repository dependencies and are discarded by Palomar verification.

## Evidence that must remain distinct

1. **Lean build and transitive axiom audits:** check proof terms for the
   audited Lean declarations and recorded source snapshot. The updated
   package passed its complete Linux build and all 33 transitive axiom audits,
   including the compared declaration, at source commit
   `261302eb6c6d2c37f726e92801ff7f790e8dcbc1`. See the
   [new Linux verification record](../verification/ci/34396410088/README.md).
   The earlier `verification/result.json`, `verification/axioms.log`, and
   [historical Linux record](../verification/ci/34373116757/README.md) remain
   evidence for their recorded snapshots, not for later edits.
2. **Comparator with independent NanoDa checking:** verifies that the selected
   Solution declaration implements the Challenge declaration under the
   permitted foundations. This check passed for the compatibility fix in
   [Linux CI run 34396410088](../verification/ci/34396410088/README.md), checking
   source commit `261302eb6c6d2c37f726e92801ff7f790e8dcbc1`.
   Both NanoDa and Lean's default kernel accepted the exported Solution.
   The [earlier successful run](../verification/ci/34373116757/README.md) checked
   commit `f813b5c3c14ddda0cd0dc429e657b0dbe6f94079` on 9 September 2026.
   The logs and tool revisions are preserved with each verification record.
3. **Palomar mechanical verification and Challenge rendering:** are server-side
   outcomes tied to a public repository, exact commit, and selected
   configuration. Local checks do not constitute either outcome. The
   [latest official mechanical record](../verification/palomar/34398823705/README.md)
   confirms success for `d98e7f29472bf79e350712f710b5c19be7f8db76`, including
   NanoDa and Lean replay with no errors or warnings. The
   [separate official rendering record](../verification/renderability/server/34401370525/README.md)
   confirms full rendering success for that same commit. The earlier
   rendering failure for `7686734` concerns the historical source without the
   compatibility fix.
4. **Automated review:** follows mechanical and rendering checks and is a
   separate judgment. Its completion is not established for the withdrawn
   submission by the successful records above.
5. **Registration:** follows the submitter's separate decision after review.
   The observed submission status does not establish registration.

## Rendering compatibility update and submission snapshot

The historical snapshot `76867341d4fe08702921aa12b88624ebb7831b4f` contains the
original Challenge. The [original rendering diagnosis](../verification/renderability/README.md)
reproduced a failure in Palomar's core-notation audit: copying dependencies
as opaque type proxies loses a definitional equality used by the inferred
`Fintype (ZMod 2)` instance. This audit is separate from the successful
mechanical proof verification recorded above.

Challenge and Solution now both name the existing finite-index instance:

```lean
instance indexFintype (k : ℕ) : Fintype (Index k) := inferInstance
```

This retains the inferred enumeration and supplies a named declaration that
the notation audit can use without expanding that implementation. The
selected theorem's documentation also states its real Walsh scope and
dimension `n = 2^k` explicitly, since Palomar's inline display omits the module
introduction. Fresh local verification of the changed sources passed the
complete Lean build (3,362 jobs, including Solution), all 33 transitive axiom
audits, and the proof-source scan. The trusted Verso literate build (2,610
jobs) and the unmodified official core-notation audit also passed on the
changed Challenge. The [fix verification record](../verification/renderability/fix/)
keeps their evidence separate from the historical passing proof checks and
the original failing rendering diagnostic. The fresh
[Linux CI run](../verification/ci/34396410088/README.md) also passed Comparator,
NanoDa, and Lean replay for source commit
`261302eb6c6d2c37f726e92801ff7f790e8dcbc1`. The subsequent official
Palomar run on `d98e7f29472bf79e350712f710b5c19be7f8db76` supplies the complete
server rendering result separately. Neither proof checking nor rendering
success establishes automated-review acceptance or registration.

The corrected snapshot `d98e7f29472bf79e350712f710b5c19be7f8db76` has now been
submitted and passed official mechanical verification and full rendering,
as recorded above. That submission was withdrawn during rendering setup,
before the successful rendering result arrived. Each
submission selects an exact commit; a push does not replace the source of an
existing submission. No automated-review acceptance or registration of the
changed source is claimed.

The metadata identifies the human author and maintainer, discloses substantive
AI work and separate automated reviews, and states that no independent human
peer review is recorded. The previous technical report is the formalized
mathematical source. The Simons workshop paper is separately credited as the
problem source. Reused formalization infrastructure is credited separately
from mathematical sources. This is the policy's source-based provenance
mode; it is not a claim that the problem collection contains our proof.

No green local check establishes publication priority, novelty, or acceptance
by Palomar. Any status summary must identify which of the above checks ran
and which exact snapshot it checked.

