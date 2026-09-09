# Challenge renderability diagnostic

**Latest status: official mechanical verification and full Challenge
rendering passed** for corrected commit
`d98e7f29472bf79e350712f710b5c19be7f8db76`. See the
[mechanical record](../palomar/34398823705/README.md) and
[full Linux rendering record](server/34401370525/README.md).
The rendering workflow completed successfully by 20:36:43 UTC on
9 September 2026. The submitter had withdrawn the submission during setup;
that withdrawal remains in effect. Automated-review completion and
registration are not claimed. The [applied-fix record](fix/) explains the
source change and its verification.

**Historical diagnosis: the Challenge at commit `7686734` failed the Palomar
core-notation audit.** The named-instance compatibility fix has since been
applied to Challenge and Solution; [fresh evidence is recorded here](fix/).

The following records the original failing source and the investigation.
For that original source, the normal Lean build and Verso literate build
succeeded, but the official audit exited with a kernel type mismatch while
copying type dependencies into its
trusted pretty-printing environment:

```
ZMod.fintype 2 ⋯
argument has type NeZero (1 + 1)
but function has type [NeZero 2] → @Fintype (ZMod 2)
```

The official renderer runs this audit after the literate build and before HTML
generation and sanitation. That failure therefore blocked the complete render
pipeline even though the theorem source compiled normally. It is a separate
diagnostic from the earlier successful proof/Comparator/NanoDa checks.

The tested Challenge is byte-identical to repository commit
`e39e455ac36c0faaceb0c200b8a4d242b3263ed5`, SHA-256
`648a4b4ef7dcb4fe2e9a24c699a50945273aaac19319a8d5d6bf801b7686fd1b`.
The PalomarSubmission implementation used for this historical test was
`ef2fa1eadcb246c2346ddba39b52eaa53d4bb763`; Verso is pinned at
`3bdedf29bada13d8103e6c979001c51dcee210c8` for Lean 4.33.0.

These checks ran locally on Windows, using the official renderer functions to
generate a fresh trusted Lake configuration and merge dependency manifests.
The Mathlib cache was reused. They were not run inside Palomar's Linux/Landrun
sandbox and do not constitute an official submission or registry report.

A separate native-Windows issue in Verso's search-asset path handling prevents
the pristine HTML command from finishing. The ignored local preview renderer
normalizes path separators in one line; its patch and separate log are included
here. That preview contains the expected compared-theorem anchor. It is only a
generated-HTML diagnostic and does not bypass or cure the core-notation audit
failure. Its appearance was not inspected in a browser: automatic review blocked
the local preview server launch, and browser security separately rejected the
local file URL. The theorem anchor was checked in the generated HTML.
The saved preview patch has zero context; use `git apply --unidiff-zero`
(and `--ignore-space-change` if Windows line endings differ) to reproduce it.

Logs and machine-readable details are in this directory. The raw preview remains
in `.cache/render-check/project/.lake/build/palomar-render-preview/Challenge/index.html`.

## Root cause and minimal reproducer

The apparent `1 + 1` versus `2` mismatch hides the relevant implicit arguments.
The expected type uses
`@NeZero Nat (MulZeroClass.toZero Nat Nat.instMulZeroClass) 2`, while the inferred
proof uses `@NeZero Nat (Zero.ofOfNat0 Nat (instOfNatNat 0)) (1 + 1)`.
These are definitionally equal in the original environment. The audit's
[`addTypeProxy`](https://github.com/PalomarRegistry/PalomarSubmission/blob/ef2fa1eadcb246c2346ddba39b52eaa53d4bb763/scripts/core_notation_audit.lean#L67)
copies types of non-core dependencies but replaces their definitions with opaque
axioms, losing the required equality between the implicit zero instances.

This is reproducible independently of SRHT with an ordinary Mathlib theorem:

```lean
import Mathlib.Data.ZMod.Basic

theorem ordinary_zmod_card_reflexivity :
    Fintype.card (ZMod 2) = Fintype.card (ZMod 2) := rfl
```

Lean accepts this theorem. The unmodified official audit rejects it with the
same error. The source and failure output are saved as `MinimalRepro.lean.txt`
and `MinimalRepro-official.err`; `trace-zeros.err` records the expanded mismatch.
This finding does not invalidate the earlier proof, Comparator, or NanoDa results.

## Compatibility experiment on the original source

Add a name for the existing inferred finite enumeration immediately after
`abbrev Index`:

```lean
instance indexFintype (k : ℕ) : Fintype (Index k) := inferInstance
```

A copy of Challenge with this one added declaration compiles and passes the
**unmodified official core-notation audit**, which returns the full theorem
signature. The source is saved as `Challenge.named-index.lean.txt`; successful
output is in `NamedIndex-official.json`, with an empty `NamedIndex-official.err`.
The named instance keeps the existing enumeration while preventing the theorem
signature from expanding its implementation across the audit's opaque proxies.

The original recommendation was to add it identically to Challenge and Solution
and rerun the proof build, Comparator, and rendering checks. At the time of
this diagnostic, the proposed change had been tested only on the copied
Challenge; the complete proof/Comparator workflow had not yet been rerun.
Those original tests
left the project sources unchanged. See the [subsequent fix record](fix/) for
the applied change and its verification.

## Other display checks

- The historical Challenge had 85 lines and 4,306 bytes, within the renderer's inline
  limits of 100 lines and 32 KiB, and selects exactly one compared theorem.
- Its explicit theorem name has the required generated anchor
  `RerandomizedSTT___problem_5_6` and binding
  `const-RerandomizedSTT.problem_5_6`.
- Backticked formulas in the documentation are ordinary Markdown under the
  current default documentation settings; they are not a rendering blocker.
- The inline renderer retains only the selected theorem and its immediate
  documentation. The original recommendation was to add **Walsh** to that
  theorem's documentation because the qualifier appeared only in the hidden
  module introduction. The applied fix includes this clarification.
- The native Windows asset-path failure is separate from Palomar's Linux
  rendering environment. Only the core-notation failure has been reproduced
  as a blocker in the platform-independent Lean audit.
