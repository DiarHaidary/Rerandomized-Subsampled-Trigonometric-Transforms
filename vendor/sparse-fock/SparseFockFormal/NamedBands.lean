import SparseFockFormal.GlobalBands
import Mathlib.Tactic

/-!
# Named physical band families

The paper uses the names `L`, `X`, `Y`, and `H` for the sixteen oriented
local products.  `GlobalBands` already proves the exhaustive nine-cell
partition; this file identifies every cell with the exact named sum appearing
in equations (light-heavy-defs), (mixed-defs), and (exact-inventory).
-/

namespace SparseFock.NamedBands

open BandInventory GlobalBands ExternalOperator

noncomputable section

variable {d m n : ℕ}

abbrev Physical (d m n : ℕ) := FullOp d m n

def wordSum (m : ℕ) (u : Fin n → Fin d → ℝ) (a b : Leg) :
    Physical d m n :=
  physicalWordSum m u (a, b)

def Lplus (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .pUp .pUp

def Lzero (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .pUp .pDown + wordSum m u .pDown .pUp

def Lminus (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .pDown .pDown

def Hplus (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .rUp .rUp

def Hzero (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .rUp .rDown + wordSum m u .rDown .rUp

def Hminus (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .rDown .rDown

def Xplus (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .pUp .rUp

def Yplus (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .rUp .pUp

def Xzero (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .pUp .rDown

def Yzero (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .rDown .pUp

def XplusAdj (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .rDown .pDown

def YplusAdj (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .pDown .rDown

def XzeroAdj (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .rUp .pDown

def YzeroAdj (m : ℕ) (u : Fin n → Fin d → ℝ) : Physical d m n :=
  wordSum m u .pDown .rUp

theorem family_plus_lightLight (u : Fin n → Fin d → ℝ) :
    family m u .plus .lightLight = Lplus m u := by
  rw [family, show wordsIn .plus .lightLight = {(.pUp, .pUp)} by decide]
  simp [family, Lplus, wordSum]

theorem family_plus_lightHeavy (u : Fin n → Fin d → ℝ) :
    family m u .plus .lightHeavy = Xplus m u + Yplus m u := by
  rw [family, show wordsIn .plus .lightHeavy = {(.pUp, .rUp), (.rUp, .pUp)} by decide]
  simp [family, Xplus, Yplus, wordSum, add_comm]

theorem family_plus_heavyHeavy (u : Fin n → Fin d → ℝ) :
    family m u .plus .heavyHeavy = Hplus m u := by
  rw [family, show wordsIn .plus .heavyHeavy = {(.rUp, .rUp)} by decide]
  simp [family, Hplus, wordSum]

theorem family_zero_lightLight (u : Fin n → Fin d → ℝ) :
    family m u .zero .lightLight = Lzero m u := by
  rw [family, show wordsIn .zero .lightLight =
    {(.pUp, .pDown), (.pDown, .pUp)} by decide]
  simp [family, Lzero, wordSum, add_comm]

theorem family_zero_lightHeavy (u : Fin n → Fin d → ℝ) :
    family m u .zero .lightHeavy =
      Xzero m u + XzeroAdj m u + Yzero m u + YzeroAdj m u := by
  rw [family, show wordsIn .zero .lightHeavy =
    {(.pUp, .rDown), (.rUp, .pDown), (.rDown, .pUp), (.pDown, .rUp)} by decide]
  simp [family, Xzero, XzeroAdj, Yzero, YzeroAdj, wordSum]
  abel

theorem family_zero_heavyHeavy (u : Fin n → Fin d → ℝ) :
    family m u .zero .heavyHeavy = Hzero m u := by
  rw [family, show wordsIn .zero .heavyHeavy =
    {(.rUp, .rDown), (.rDown, .rUp)} by decide]
  simp [family, Hzero, wordSum, add_comm]

theorem family_minus_lightLight (u : Fin n → Fin d → ℝ) :
    family m u .minus .lightLight = Lminus m u := by
  rw [family, show wordsIn .minus .lightLight = {(.pDown, .pDown)} by decide]
  simp [family, Lminus, wordSum]

theorem family_minus_lightHeavy (u : Fin n → Fin d → ℝ) :
    family m u .minus .lightHeavy = XplusAdj m u + YplusAdj m u := by
  rw [family, show wordsIn .minus .lightHeavy =
    {(.rDown, .pDown), (.pDown, .rDown)} by decide]
  simp [family, XplusAdj, YplusAdj, wordSum, add_comm]

theorem family_minus_heavyHeavy (u : Fin n → Fin d → ℝ) :
    family m u .minus .heavyHeavy = Hminus m u := by
  rw [family, show wordsIn .minus .heavyHeavy = {(.rDown, .rDown)} by decide]
  simp [family, Hminus, wordSum]

/-- The paper's displayed `+2` inventory formula. -/
theorem band_plus_named (u : Fin n → Fin d → ℝ) (ρ : ℝ) :
    band m u ρ .plus =
      Lplus m u + ρ • (Xplus m u + Yplus m u) + ρ ^ 2 • Hplus m u := by
  rw [band_eq_three_families, family_plus_lightLight,
    family_plus_lightHeavy, family_plus_heavyHeavy]

/-- The paper's displayed grade-zero inventory formula. -/
theorem band_zero_named (u : Fin n → Fin d → ℝ) (ρ : ℝ) :
    band m u ρ .zero = Lzero m u +
      ρ • (Xzero m u + XzeroAdj m u + Yzero m u + YzeroAdj m u) +
      ρ ^ 2 • Hzero m u := by
  rw [band_eq_three_families, family_zero_lightLight,
    family_zero_lightHeavy, family_zero_heavyHeavy]

/-- The paper's displayed `-2` inventory formula. -/
theorem band_minus_named (u : Fin n → Fin d → ℝ) (ρ : ℝ) :
    band m u ρ .minus =
      Lminus m u + ρ • (XplusAdj m u + YplusAdj m u) +
        ρ ^ 2 • Hminus m u := by
  rw [band_eq_three_families, family_minus_lightLight,
    family_minus_lightHeavy, family_minus_heavyHeavy]

end

end SparseFock.NamedBands
