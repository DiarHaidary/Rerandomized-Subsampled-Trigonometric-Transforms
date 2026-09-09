# Palomar layout and verification boundaries

Prepared against the official [submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/e9c8c238f5695b10f75db7175648a1d0195352c1/CONTRIBUTING.md)
and [starter template](https://github.com/PalomarRegistry/PalomarTemplate/tree/128a6c5ce5f48622e69927ccd639cbff401022e8),
inspected on 9 September 2026. A later Palomar submission must use the policy
and verifier active when submitted; this document records the preparation
basis, not an acceptance decision.

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
   audited Lean declarations and recorded source snapshot. The new package passed its complete build and all 33 transitive axiom audits on 9 September 2026, including the compared declaration. See `verification/result.json` and `verification/axioms.log`.
2. **Comparator with independent NanoDa checking:** verifies that the selected
   Solution declaration implements the Challenge declaration under the
   permitted foundations. It is a separate check from compilation. Use the
   pinned verification script or CI; preserve their actual outcomes.
3. **Palomar mechanical verification and editorial review:** are server-side
   outcomes tied to a public repository, exact commit, and selected
   configuration. Local checks do not constitute either outcome.
4. **Registration:** follows the submitter's separate decision after review.
   Creating this repository does not submit or register it.

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

