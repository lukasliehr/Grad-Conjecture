import AEM3UniformOriginalLowOuterEstimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.AnnularSourceGraph Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

def lowOuterHalfFamily (lower length : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (field : lowEnergyGraph lower length positive) : LowEnergyBoundary :=
  ⟨lowOuterHalfCoefficient lower length positive lowerHalf field,
    (lp.memℓp ((lowOuterHalfConstant : ℝ) • (lpNormFamily (field.val 0) + lpNormFamily (field.val 1)))).mono'
      (fun index => by
        change ‖lowOuterHalfCoefficient lower length positive lowerHalf field index‖ ≤
          ‖lowOuterHalfConstant • (‖field.val 0 index‖ + ‖field.val 1 index‖)‖
        rw [norm_smul, Real.norm_of_nonneg lowOuterHalfConstant_nonnegative,
          Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
        exact lowOuterHalfCoefficient_bound lower length positive lowerHalf field index)⟩

theorem lowOuterHalfFamily_bound (lower length : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (field : lowEnergyGraph lower length positive) :
    ‖lowOuterHalfFamily lower length positive lowerHalf field‖ ≤ lowOuterHalfConstant * (‖field.val 0‖ + ‖field.val 1‖) := by
  calc
    _ ≤ ‖lowOuterHalfConstant • (lpNormFamily (field.val 0) + lpNormFamily (field.val 1))‖ := by
      apply lp.norm_mono (by norm_num)
      intro index
      change ‖lowOuterHalfCoefficient lower length positive lowerHalf field index‖ ≤
        ‖lowOuterHalfConstant • (‖field.val 0 index‖ + ‖field.val 1 index‖)‖
      rw [norm_smul, Real.norm_of_nonneg lowOuterHalfConstant_nonnegative,
        Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact lowOuterHalfCoefficient_bound lower length positive lowerHalf field index
    _ = lowOuterHalfConstant * ‖lpNormFamily (field.val 0) + lpNormFamily (field.val 1)‖ := by
      rw [norm_smul, Real.norm_of_nonneg lowOuterHalfConstant_nonnegative]
    _ ≤ lowOuterHalfConstant * (‖lpNormFamily (field.val 0)‖ + ‖lpNormFamily (field.val 1)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) lowOuterHalfConstant_nonnegative
    _ = _ := by rw [lpNormFamily_norm, lpNormFamily_norm]

def lowOuterHalfLinear (lower length : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) :
    lowEnergyGraph lower length positive →ₗ[ℂ] LowEnergyBoundary where
  toFun := lowOuterHalfFamily lower length positive lowerHalf
  map_add' first second := by
    apply lp.ext
    funext index
    change lowOuterHalfCoefficient lower length positive lowerHalf (first + second) index =
      lowOuterHalfCoefficient lower length positive lowerHalf first index + lowOuterHalfCoefficient lower length positive lowerHalf second index
    unfold lowOuterHalfCoefficient lowEnergyEndpoint
    rw [lowEnergySection_add]
    exact smul_add _ _ _
  map_smul' scalar field := by
    apply lp.ext
    funext index
    change lowOuterHalfCoefficient lower length positive lowerHalf (scalar • field) index =
      scalar • lowOuterHalfCoefficient lower length positive lowerHalf field index
    unfold lowOuterHalfCoefficient lowEnergyEndpoint
    rw [lowEnergySection_smul]
    exact smul_comm ((Real.sqrt (lowMu length (1 / 2) index.2.val.2))⁻¹ : ℝ) scalar
      (lowEnergyEndpoint lower length positive (lowerHalf.trans_lt (by norm_num)) 1 field index)

theorem lowOuterHalfLinear_bound (lower length : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (field : lowEnergyGraph lower length positive) :
    ‖lowOuterHalfLinear lower length positive lowerHalf field‖ ≤ (2 * lowOuterHalfConstant) * ‖field‖ := by
  have first := lowStoredCoordinate_bound lower length positive 0 field
  have second := lowStoredCoordinate_bound lower length positive 1 field
  change ‖field.val 0‖ ≤ ‖field‖ at first
  change ‖field.val 1‖ ≤ ‖field‖ at second
  exact (lowOuterHalfFamily_bound lower length positive lowerHalf field).trans
    ((mul_le_mul_of_nonneg_left (by linarith : ‖field.val 0‖ + ‖field.val 1‖ ≤ 2 * ‖field‖)
      lowOuterHalfConstant_nonnegative).trans_eq (by ring))

/-- Actual complete outer trace of arbitrary Y, normalized at a fixed half
collar. All norm constants are independent of the original inner radius. -/
def lowOuterHalfTrace (lower length : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) :
    lowEnergyGraph lower length positive →L[ℂ] LowEnergyBoundary :=
  (lowOuterHalfLinear lower length positive lowerHalf).mkContinuous (2 * lowOuterHalfConstant)
    (lowOuterHalfLinear_bound lower length positive lowerHalf)

theorem lowOuterHalfTrace_apply (lower length : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    lowOuterHalfTrace lower length positive lowerHalf field index =
      (Real.sqrt (lowMu length (1 / 2) index.2.val.2))⁻¹ •
        lowEnergyEndpoint lower length positive (lowerHalf.trans_lt (by norm_num)) 1 field index := rfl

end Grad.AnnularCrossMaps
