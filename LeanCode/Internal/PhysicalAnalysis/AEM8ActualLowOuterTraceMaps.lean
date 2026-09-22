import AEM7LiteralLowBoundaryCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.BoundaryKernelAction

/-- A bounded scalar family on the actual four low modes and every cell. -/
def lowBoundaryMultiplier (coefficient : LowAnnularMode → ℝ) (bound : ℝ)
    (nonnegative : 0 ≤ bound) (bounded : ∀ mode, |coefficient mode| ≤ bound) :
    LowModeBoundary →L[ℂ] LowModeBoundary :=
  complexLpTwoMap (fun mode => coefficient mode • ContinuousLinearMap.id ℂ (ComplexEuclidean 1))
    bound nonnegative (fun mode field => by
      change ‖coefficient mode • field‖ ≤ bound * ‖field‖
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (bounded mode) (norm_nonneg _))

theorem lowBoundaryMultiplier_apply (coefficient : LowAnnularMode → ℝ) (bound : ℝ)
    (nonnegative : 0 ≤ bound) (bounded : ∀ mode, |coefficient mode| ≤ bound)
    (field : LowModeBoundary) (mode : LowAnnularMode) :
    lowBoundaryMultiplier coefficient bound nonnegative bounded field mode = coefficient mode • field mode := rfl

theorem lowBoundaryMultiplier_bound (coefficient : LowAnnularMode → ℝ) (bound : ℝ)
    (nonnegative : 0 ≤ bound) (bounded : ∀ mode, |coefficient mode| ≤ bound)
    (field : LowModeBoundary) :
    ‖lowBoundaryMultiplier coefficient bound nonnegative bounded field‖ ≤ bound * ‖field‖ :=
  complexLpTwoMap_bound _ _ _ _ field

/-- The literal negative-half outer trace of x, obtained from the canonical
weak low graph representative. There are no free boundary coordinates. -/
def lowOuterXNegative (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) :
    lowEnergyGraph lower length positive →L[ℂ] NegativeTrace parameters 0 0 1 :=
  lowBoundaryIntoFull.toContinuousLinearMap ∘L
    lowBoundaryMultiplier (lowOuterNegativeFactor length) (lowOuterFrequencyConstant length)
      (by linarith [lowOuterFrequencyConstant_two_le length lengthPositive])
      (lowOuterNegativeFactor_bound length lengthPositive) ∘L
    lowBoundaryComponent 1 ∘L lowOuterHalfTrace lower length positive lowerHalf

/-- The literal positive-half outer trace of xi, with its original a_m*mu
coordinate and the same analytic phase. -/
def lowOuterXiPositive (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) :
    lowEnergyGraph lower length positive →L[ℂ] PositiveTrace parameters 0 0 1 :=
  lowBoundaryIntoFull.toContinuousLinearMap ∘L
    lowBoundaryMultiplier (lowOuterPositiveFactor parameters length) (2 * lowOuterFrequencyConstant length)
      (by linarith [lowOuterFrequencyConstant_two_le length lengthPositive])
      (lowOuterPositiveFactor_bound parameters length lengthPositive) ∘L
    lowBoundaryComponent 0 ∘L lowOuterHalfTrace lower length positive lowerHalf

theorem lowOuterXNegative_bound (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (field : lowEnergyGraph lower length positive) :
    ‖lowOuterXNegative parameters lower length lengthPositive positive lowerHalf field‖ ≤
      (2 * lowOuterFrequencyConstant length * lowOuterHalfConstant) * ‖field‖ := by
  unfold lowOuterXNegative
  simp only [ContinuousLinearMap.comp_apply]
  change ‖lowBoundaryExtension _‖ ≤ _
  rw [lowBoundaryExtension_norm]
  apply (lowBoundaryMultiplier_bound _ _ _ _ _).trans
  have constant : 0 ≤ lowOuterFrequencyConstant length := by linarith [lowOuterFrequencyConstant_two_le length lengthPositive]
  calc
    _ ≤ lowOuterFrequencyConstant length * ‖lowOuterHalfTrace lower length positive lowerHalf field‖ :=
      mul_le_mul_of_nonneg_left (lowBoundaryComponent_bound 1 _) constant
    _ ≤ lowOuterFrequencyConstant length * ((2 * lowOuterHalfConstant) * ‖field‖) :=
      mul_le_mul_of_nonneg_left (lowOuterHalfLinear_bound lower length positive lowerHalf field) constant
    _ = _ := by ring

theorem lowOuterXiPositive_bound (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (field : lowEnergyGraph lower length positive) :
    ‖lowOuterXiPositive parameters lower length lengthPositive positive lowerHalf field‖ ≤
      (4 * lowOuterFrequencyConstant length * lowOuterHalfConstant) * ‖field‖ := by
  unfold lowOuterXiPositive
  simp only [ContinuousLinearMap.comp_apply]
  change ‖lowBoundaryExtension _‖ ≤ _
  rw [lowBoundaryExtension_norm]
  apply (lowBoundaryMultiplier_bound _ _ _ _ _).trans
  have constant : 0 ≤ 2 * lowOuterFrequencyConstant length := by linarith [lowOuterFrequencyConstant_two_le length lengthPositive]
  calc
    _ ≤ (2 * lowOuterFrequencyConstant length) * ‖lowOuterHalfTrace lower length positive lowerHalf field‖ :=
      mul_le_mul_of_nonneg_left (lowBoundaryComponent_bound 0 _) constant
    _ ≤ (2 * lowOuterFrequencyConstant length) * ((2 * lowOuterHalfConstant) * ‖field‖) :=
      mul_le_mul_of_nonneg_left (lowOuterHalfLinear_bound lower length positive lowerHalf field) constant
    _ = _ := by ring

theorem lowOuterXNegative_retained (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (field : lowEnergyGraph lower length positive) (mode : LowAnnularMode) :
    lowOuterXNegative parameters lower length lengthPositive positive lowerHalf field mode.val =
      lowOuterNegativeFactor length mode • ((Real.sqrt (lowMu length (1 / 2) mode.val.2))⁻¹ •
        lowEnergyEndpoint lower length positive (lowerHalf.trans_lt (by norm_num)) 1 field (1, mode)) :=
  lowBoundaryIntoFull_retained _ _

theorem lowOuterXiPositive_retained (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (field : lowEnergyGraph lower length positive) (mode : LowAnnularMode) :
    lowOuterXiPositive parameters lower length lengthPositive positive lowerHalf field mode.val =
      lowOuterPositiveFactor parameters length mode • ((Real.sqrt (lowMu length (1 / 2) mode.val.2))⁻¹ •
        lowEnergyEndpoint lower length positive (lowerHalf.trans_lt (by norm_num)) 1 field (0, mode)) :=
  lowBoundaryIntoFull_retained _ _

theorem lowOuterXNegative_outside (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (field : lowEnergyGraph lower length positive) (mode : ℤ × ℤ)
    (outside : ¬ (|mode.1| = 1 ∨ |mode.1| = 2)) :
    lowOuterXNegative parameters lower length lengthPositive positive lowerHalf field mode = 0 :=
  lowBoundaryIntoFull_outside _ _ outside

theorem lowOuterXiPositive_outside (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (field : lowEnergyGraph lower length positive) (mode : ℤ × ℤ)
    (outside : ¬ (|mode.1| = 1 ∨ |mode.1| = 2)) :
    lowOuterXiPositive parameters lower length lengthPositive positive lowerHalf field mode = 0 :=
  lowBoundaryIntoFull_outside _ _ outside

end Grad.AnnularCrossMaps
