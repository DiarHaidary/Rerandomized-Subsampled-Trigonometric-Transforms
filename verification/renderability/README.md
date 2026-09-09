# Challenge renderability diagnostic

**The current Challenge does not pass the current Palomar core-notation audit.**
The normal Lean build and Verso literate build succeed, but the official audit
exits with a kernel type mismatch while copying type dependencies into its
trusted pretty-printing environment:

```
ZMod.fintype 2 ⋯
argument has type NeZero (1 + 1)
but function has type [NeZero 2] → @Fintype (ZMod 2)
```

The official renderer runs this audit after the literate build and before HTML
generation and sanitation. This failure therefore blocks the complete render
pipeline even though the theorem source compiles normally. It is a separate
diagnostic from the earlier successful proof/Comparator/NanoDa checks.

The tested Challenge is byte-identical to repository commit
`e39e455ac36c0faaceb0c200b8a4d242b3263ed5`, SHA-256
`648a4b4ef7dcb4fe2e9a24c699a50945273aaac19319a8d5d6bf801b7686fd1b`.
The current PalomarSubmission implementation tested is
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

## Tested compatibility fix, not applied to project sources

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

If adopting this change, add it identically to Challenge and Solution and rerun
the proof build, Comparator, and rendering checks. The proposed change has been
tested only on the copied Challenge; the complete proof/Comparator workflow has
not been rerun with it. The actual Challenge, Solution, and proof sources remain
unchanged.

## Other display checks

- Current Challenge has 85 lines and 4,306 bytes, within the renderer's inline
  limits of 100 lines and 32 KiB, and selects exactly one compared theorem.
- Its explicit theorem name has the required generated anchor
  `RerandomizedSTT___problem_5_6` and binding
  `const-RerandomizedSTT.problem_5_6`.
- Backticked formulas in the documentation are ordinary Markdown under the
  current default documentation settings; they are not a rendering blocker.
- The inline renderer retains only the selected theorem and its immediate
  documentation. For clarity, add the word **Walsh** to that theorem's
  documentation: the current Walsh qualifier appears only in the module
  introduction, which the inline view hides.
- The native Windows asset-path failure is separate from Palomar's Linux
  rendering environment. Only the core-notation failure has been reproduced
  as a blocker in the platform-independent Lean audit.
