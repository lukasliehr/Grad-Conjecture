import GC18APLinearity

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

theorem apAllocatedOperator_add {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ} (allocation : APAllocation grade)
    (first second : WeightedAmbient grade inputDimension outputDimension) :
    apAllocatedOperator admissible allocation (first + second) =
      apAllocatedOperator admissible allocation first + apAllocatedOperator admissible allocation second := by
  unfold apAllocatedOperator
  simp only [lp.coeFn_add, Pi.add_apply, apSingleOperator_add]
  exact ((apSingleOperator_norm_summable admissible allocation first).of_norm).tsum_add
    ((apSingleOperator_norm_summable admissible allocation second).of_norm)

theorem apAllocatedOperator_smul {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ} (allocation : APAllocation grade) (scalar : ℂ)
    (coefficient : WeightedAmbient grade inputDimension outputDimension) :
    apAllocatedOperator admissible allocation (scalar • coefficient) =
      scalar • apAllocatedOperator admissible allocation coefficient := by
  unfold apAllocatedOperator
  simp only [lp.coeFn_smul, Pi.smul_apply, apSingleOperator_smul]
  exact (apSingleOperator_norm_summable admissible allocation coefficient).of_norm.tsum_const_smul scalar

theorem apAmbientMultiplier_add {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ} (first second : WeightedAmbient grade inputDimension outputDimension) :
    apAmbientMultiplier admissible (first + second) = apAmbientMultiplier admissible first + apAmbientMultiplier admissible second := by
  simp only [apAmbientMultiplier, apAllocatedOperator_add, smul_add, Finset.sum_add_distrib]

theorem apAmbientMultiplier_smul {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ} (scalar : ℂ) (coefficient : WeightedAmbient grade inputDimension outputDimension) :
    apAmbientMultiplier admissible (scalar • coefficient) = scalar • apAmbientMultiplier admissible coefficient := by
  simp only [apAmbientMultiplier, apAllocatedOperator_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro allocation _
  exact smul_comm _ _ _

/-- Bounded bilinear action in the original weighted coefficient and AP2
derivative-array norms. The core realization is supplied separately. -/
def apAmbientBilinear {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (inputDimension outputDimension grade : ℕ) :
    WeightedAmbient grade inputDimension outputDimension →L[ℂ]
      APAmbient inputDimension grade →L[ℂ] APAmbient outputDimension grade :=
  let mapping : WeightedAmbient grade inputDimension outputDimension →ₗ[ℂ]
      (APAmbient inputDimension grade →L[ℂ] APAmbient outputDimension grade) :=
    { toFun := apAmbientMultiplier admissible
      map_add' := apAmbientMultiplier_add admissible
      map_smul' := apAmbientMultiplier_smul admissible }
  @LinearMap.mkContinuous ℂ ℂ (WeightedAmbient grade inputDimension outputDimension)
    (APAmbient inputDimension grade →L[ℂ] APAmbient outputDimension grade)
    _ _ _ _ _ _ (RingHom.id ℂ) mapping (apMultiplierConstant L sigma gamma grade)
      (apAmbientMultiplier_norm_le admissible)

end Grad.GaugeCoefficients.Physical.RadialLedger
