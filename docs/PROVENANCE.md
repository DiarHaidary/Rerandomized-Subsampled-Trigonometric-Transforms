# Provenance of the packaged development

The full SRHT proof sources were copied from the completed local Lean project
into this repository without changing the mathematical development. The new
Challenge/Solution interface presents the same independent-sign theorem using
transparent Mathlib-only definitions in the Challenge. The solution's finite
uniform average is proved equal to the existing product-law probability.

The informal report is the project's revised 7 September 2026 report. Its
Markdown, LaTeX, and PDF forms are preserved in this directory. They describe
the proof and are not replacements for the Lean sources. Historical local
paths in the report and audit notes identify the original development
locations; a clean build requires only this repository and its pinned public
dependencies. The paper arXiv:2602.05394v3 is linked, not redistributed.

## Reused sources

The 55 vendored Lean modules were inherited from the author's earlier
[Nelson–Nguyen sparse-Fock repository](https://github.com/DiarHaidary/nelson-nguyen-sparse-fock),
revision `3a8969bfa135b7b5042d7090df992780b8ac567b`. They retain their original
namespaces. `FiniteLocalMoments.lean` comes from the limited-independence
extension; the other modules come from the main formal development.
These are source proofs, not postulated estimates. The MIT copyright notice
is preserved at `vendor/sparse-fock/LICENSE`.

[source-provenance.json](source-provenance.json) records each included module's
SHA-256, its matching committed upstream path, the unchanged SRHT proof
sources, and the three informal report hashes. Matching allows only line-ending
normalization. These provenance hashes describe the copied source bytes;
the build and Comparator records separately identify the sources they checked.

The full vendored library is retained for provenance and reproducibility.
The selected theorem uses the dependency closure reached by its proof;
shipping another file does not make its declarations part of that closure.

## Packaging references

The layout follows the official
[PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate/tree/128a6c5ce5f48622e69927ccd639cbff401022e8)
and [PalomarPolicy](https://github.com/PalomarRegistry/PalomarPolicy/tree/e9c8c238f5695b10f75db7175648a1d0195352c1)
inspected on 9 September 2026. The confined verification scripts are adapted
from the author's related Graph Matrices packaging and pin their actual
upstream tools in `scripts/tool-pins.json`. The copied template is reference
material only; this repository does not contain its toy theorem.

Diar Heidary directed the project. Codex and AI subagents performed substantial
research, formalization, packaging, and statement auditing. This is disclosed
in `formalization.yaml`. No independent human mathematical review, publication
priority, or Palomar registration is asserted.
