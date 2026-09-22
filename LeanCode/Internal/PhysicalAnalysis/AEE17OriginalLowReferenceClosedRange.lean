import AEE16CompleteOriginalLowCoercivity

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Function
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.AnnularLowEnergy Grad.AnnularLowVolterra Grad.CartesianState

theorem lowReferenceDataOperator_antilipschitz (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1) :
    AntilipschitzWith ⟨Real.sqrt (lowReferenceGraphConstant parameters length), Real.sqrt_nonneg _⟩
      (lowReferenceDataOperator parameters length lower lengthPositive positive bounded) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro first second
  change dist first second ≤ Real.sqrt (lowReferenceGraphConstant parameters length) *
    dist (lowReferenceDataOperator parameters length lower lengthPositive positive bounded first)
      (lowReferenceDataOperator parameters length lower lengthPositive positive bounded second)
  simpa only [dist_eq_norm, map_sub] using
    lowReferenceDataOperator_lowerBound parameters length lower lengthPositive positive bounded (first - second)

theorem lowReferenceDataOperator_injective (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1) :
    Function.Injective (lowReferenceDataOperator parameters length lower lengthPositive positive bounded) :=
  (lowReferenceDataOperator_antilipschitz parameters length lower lengthPositive positive bounded).injective

theorem lowReferenceDataOperator_closed_range (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1) :
    IsClosed (Set.range (lowReferenceDataOperator parameters length lower lengthPositive positive bounded)) :=
  (lowReferenceDataOperator_antilipschitz parameters length lower lengthPositive positive bounded).isClosed_range
    (lowReferenceDataOperator parameters length lower lengthPositive positive bounded).uniformContinuous

end Grad.AnnularLowCompletion
