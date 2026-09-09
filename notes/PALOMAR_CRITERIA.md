# Palomar layout and verification boundaries

Prepared against the official [submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/e9c8c238f5695b10f75db7175648a1d0195352c1/CONTRIBUTING.md)
and [starter template](https://github.com/PalomarRegistry/PalomarTemplate/tree/128a6c5ce5f48622e69927ccd639cbff401022e8),
inspected on 9 September 2026. Each Palomar submission uses the policy and
verifier active when submitted; this document records the preparation basis
and observed status, not an acceptance decision.

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
   audited Lean declarations and recorded source snapshot. The historical
   package passed its complete build and all 33 transitive axiom audits on
   9 September 2026, including the compared declaration. See
   `verification/result.json`, `verification/axioms.log`, and the exact-commit
   Linux record below. Those results do not by themselves verify later edits.
2. **Comparator with independent NanoDa checking:** verifies that the selected
   Solution declaration implements the Challenge declaration under the
   permitted foundations. This check passed in
   [Linux CI run 34373116757](../verification/ci/34373116757/README.md) for
   commit `f813b5c3c14ddda0cd0dc429e657b0dbe6f94079` on 9 September 2026.
   Both NanoDa and Lean's default kernel accepted the exported Solution;
   the active confinement controls also passed. The complete logs and tool
   revisions are preserved with the verification record.
3. **Palomar mechanical verification and editorial review:** are server-side
   outcomes tied to a public repository, exact commit, and selected
   configuration. Local checks do not constitute either outcome. The
   submitter's status-page screenshot records mechanical verification success
   for commit `76867341d4fe08702921aa12b88624ebb7831b4f` at 18:00:19 UTC on
   9 September 2026. It subsequently records a Challenge-rendering retry at
   19:14:51 UTC; it does not establish completion of automated review.
4. **Registration:** follows the submitter's separate decision after review.
   The observed submission status does not establish registration.

## Rendering compatibility update and submission snapshot

The submitted snapshot `76867341d4fe08702921aa12b88624ebb7831b4f` contains the
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
the original failing rendering diagnostic. A fresh Comparator/NanoDa CI run
is still pending. These scoped local successes do not establish a complete
Linux rendering-gate pass or Palomar acceptance.

The status page records submission at 17:48:26 UTC on 9 September 2026 and
selects the old exact commit. A push does not update that selected snapshot.
To check the compatibility change, a submission must select the new public
commit containing it. No automated-review acceptance or registration of the
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

