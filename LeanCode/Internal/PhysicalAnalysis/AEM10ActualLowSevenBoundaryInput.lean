import AEM9LiteralPhysicalOuterTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.BoundaryKernelAction Grad.PhaseAlgebra Grad.BoundaryTrace

variable (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)

def lowOuterSevenLinear : lowEnergyGraph lower length positive →ₗ[ℂ] SevenSlotTrace parameters 0 0 where
  toFun field := actualSevenSlotTrace parameters length 0 0
    (lowOuterXNegative parameters lower length lengthPositive positive lowerHalf field)
    (lowOuterXiPositive parameters lower length lengthPositive positive lowerHalf field) 0
  map_add' := by
    intro first second
    apply PiLp.ext
    intro slot
    have left := actualSevenSlotTrace_components parameters length 0 0
      (lowOuterXNegative parameters lower length lengthPositive positive lowerHalf (first + second))
      (lowOuterXiPositive parameters lower length lengthPositive positive lowerHalf (first + second)) 0
    have firstComponents := actualSevenSlotTrace_components parameters length 0 0
      (lowOuterXNegative parameters lower length lengthPositive positive lowerHalf first)
      (lowOuterXiPositive parameters lower length lengthPositive positive lowerHalf first) 0
    have secondComponents := actualSevenSlotTrace_components parameters length 0 0
      (lowOuterXNegative parameters lower length lengthPositive positive lowerHalf second)
      (lowOuterXiPositive parameters lower length lengthPositive positive lowerHalf second) 0
    simp only [PiLp.add_apply, congrFun left slot, congrFun firstComponents slot, congrFun secondComponents slot]
    fin_cases slot <;> simp [map_add]
  map_smul' := by
    intro scalar field
    apply PiLp.ext
    intro slot
    have left := actualSevenSlotTrace_components parameters length 0 0
      (lowOuterXNegative parameters lower length lengthPositive positive lowerHalf (scalar • field))
      (lowOuterXiPositive parameters lower length lengthPositive positive lowerHalf (scalar • field)) 0
    have right := actualSevenSlotTrace_components parameters length 0 0
      (lowOuterXNegative parameters lower length lengthPositive positive lowerHalf field)
      (lowOuterXiPositive parameters lower length lengthPositive positive lowerHalf field) 0
    simp only [PiLp.smul_apply, congrFun left slot, congrFun right slot]
    fin_cases slot <;> simp [map_smul]

def lowOuterSevenConstant : ℝ := 10 * lowOuterFrequencyConstant length * lowOuterHalfConstant

omit parameters lower lengthPositive positive lowerHalf in
theorem lowOuterSevenConstant_nonnegative (lengthPositive : 0 < length) : 0 ≤ lowOuterSevenConstant length := by
  unfold lowOuterSevenConstant
  exact mul_nonneg (by linarith [lowOuterFrequencyConstant_two_le length lengthPositive]) lowOuterHalfConstant_nonnegative

theorem lowOuterSevenLinear_bound (field : lowEnergyGraph lower length positive) :
    ‖lowOuterSevenLinear parameters lower length lengthPositive positive lowerHalf field‖ ≤
      lowOuterSevenConstant length * ‖field‖ := by
  let x := lowOuterXNegative parameters lower length lengthPositive positive lowerHalf field
  let xi := lowOuterXiPositive parameters lower length lengthPositive positive lowerHalf field
  have square := actualSevenSlotTrace_bound_sq parameters length lengthPositive 0 0 x xi 0
  norm_num only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at square
  have bound : ‖lowOuterSevenLinear parameters lower length lengthPositive positive lowerHalf field‖ ≤ ‖x‖ + 2 * ‖xi‖ := by
    change ‖actualSevenSlotTrace parameters length 0 0 x xi 0‖ ≤ _
    nlinarith [norm_nonneg x, norm_nonneg xi, norm_nonneg (actualSevenSlotTrace parameters length 0 0 x xi 0), mul_nonneg (norm_nonneg x) (norm_nonneg xi)]
  have bx : ‖x‖ ≤ (2 * lowOuterFrequencyConstant length * lowOuterHalfConstant) * ‖field‖ :=
    lowOuterXNegative_bound parameters lower length lengthPositive positive lowerHalf field
  have bxi : ‖xi‖ ≤ (4 * lowOuterFrequencyConstant length * lowOuterHalfConstant) * ‖field‖ :=
    lowOuterXiPositive_bound parameters lower length lengthPositive positive lowerHalf field
  unfold lowOuterSevenConstant
  linarith

def lowOuterSevenTrace : lowEnergyGraph lower length positive →L[ℂ] SevenSlotTrace parameters 0 0 :=
  (lowOuterSevenLinear parameters lower length lengthPositive positive lowerHalf).mkContinuous
    (lowOuterSevenConstant length) (lowOuterSevenLinear_bound parameters lower length lengthPositive positive lowerHalf)

theorem lowOuterSevenTrace_apply (field : lowEnergyGraph lower length positive) :
    lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf field =
      actualSevenSlotTrace parameters length 0 0
        (lowOuterXNegative parameters lower length lengthPositive positive lowerHalf field)
        (lowOuterXiPositive parameters lower length lengthPositive positive lowerHalf field) 0 := rfl

theorem lowOuterSevenTrace_meanFree (field : lowEnergyGraph lower length positive) :
    IsAngularMeanFree parameters 0 0 (lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf field 0) := by
  intro cell
  change negativeTraceCoefficient parameters 0 0
    (lowOuterXNegative parameters lower length lengthPositive positive lowerHalf field) (0, cell) = 0
  unfold negativeTraceCoefficient
  rw [lowOuterXNegative_outside parameters lower length lengthPositive positive lowerHalf field (0, cell) (by norm_num), smul_zero]

theorem lowOuterSevenTrace_derivative (field : lowEnergyGraph lower length positive) :
    IsAngularDerivative parameters 0 0
      (lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf field 3)
      (lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf field 1) :=
  positiveToNegative_derivative parameters 0 0
    (lowOuterXiPositive parameters lower length lengthPositive positive lowerHalf field)

end Grad.AnnularCrossMaps
