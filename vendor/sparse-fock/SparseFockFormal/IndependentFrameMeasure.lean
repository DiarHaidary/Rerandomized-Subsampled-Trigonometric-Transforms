import SparseFockFormal.MainTheorem
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! Temporary scaffold for the arbitrary-measure independent-frame corollary. -/

namespace SparseFock.IndependentFrameMeasure

open MeasureTheory

#check hasSum_fintype
#check Fintype.hasSum_iff
#check Finset.hasSum_sum
#check ENNReal.coe_finset_sum
#check PMF.toMeasure_apply
#check PMF.toMeasure_apply_singleton
#check PMF.toMeasure.isProbabilityMeasure
#check ENNReal.toReal_ofReal
#check ENNReal.ofReal_sum_of_nonneg
#check MeasureTheory.Measure.prod_apply_symm
#check MeasureTheory.lintegral_le_const
#check MeasureTheory.lintegral_mono
#check MeasureTheory.lintegral_const
#check MeasureTheory.MeasureReal_def

end SparseFock.IndependentFrameMeasure
