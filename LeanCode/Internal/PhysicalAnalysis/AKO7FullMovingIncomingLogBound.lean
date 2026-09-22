import AKO6SameLowMovingIncomingTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ENNReal BigOperators
namespace Grad.AnnularIncomingIntegrability
open Grad.AnnularVariational Grad.AnnularReconstruction Grad.AnnularRestriction Grad.AnnularLowEnergy
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularInverseCalculus
open Grad.AnnularSourceGraph
open Grad.AnnularTiltedReference

variable (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)

theorem highIncomingSquare_measurable (field : annularEnergySpace lower length positive) :
    Measurable (highIncomingSquare lower length positive bounded field) := by
  apply Measurable.tsum
  intro mode
  exact (measurable_const.mul
    ((highIncomingRepresentative lower length positive bounded field mode).continuous.measurable.norm.pow_const 2)).ennreal_ofReal

/-- The incoming boundary pair in exactly the original weighted BF norms. -/
def coupledIncomingTrace (field : CoupledSpace lower length positive lengthPositive) :=
  WithLp.toLp 2
    (annularEnergyTrace lower length positive bounded lengthPositive 0
      (bEnergyDecode lower length positive field.ofLp.1.ofLp.1),
    lowIncomingTrace lower length positive bounded field.ofLp.2)

/-- Full high-plus-low incoming square of the SAME genuine representative. -/
def coupledIncomingSquare (field : CoupledSpace lower length positive lengthPositive) (radius : ℝ) : ℝ≥0∞ :=
  highIncomingSquare lower length positive bounded field.ofLp.1.ofLp.1 radius +
    lowIncomingSquare lower length positive bounded field.ofLp.2 radius

/-- No constant depends on the inner radius. Only one inserted high grade and
the original low value energy enter this fixed-collar logarithmic estimate. -/
theorem coupledIncomingSquare_log_bound
    (field weighted : CoupledSpace lower length positive lengthPositive)
    (same : CoupledInsertedGrade lower length positive lengthPositive 1 field weighted) :
    (∫⁻ radius, ENNReal.ofReal radius⁻¹ * coupledIncomingSquare lower length positive bounded lengthPositive field radius
      ∂volume.restrict (Icc lower 1)) ≤ ENNReal.ofReal (‖weighted‖ ^ 2 + ‖field‖ ^ 2) := by
  have high := highIncomingSquare_log_bound lower length positive bounded field.ofLp.1.ofLp.1 weighted.ofLp.1.ofLp.1
    (fun mode => by simpa only [pow_one] using same.1 mode)
  have low := lowIncomingSquare_log_bound lower length positive bounded field.ofLp.2
  have highBound := coupledEnergy_bound lower length positive lengthPositive weighted
  have lowBound := coupledLow_bound lower length positive lengthPositive field
  have lowSquare := lowEnergyGraph_norm_sq lower length positive field.ofLp.2
  have lowValue : ‖field.ofLp.2.val 0‖ ^ 2 ≤ ‖field‖ ^ 2 := by
    have squareBound := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr lowBound
    change ‖field.ofLp.2‖ ^ 2 ≤ ‖field‖ ^ 2 at squareBound
    nlinarith only [lowSquare,squareBound,sq_nonneg ‖field.ofLp.2.val 1‖]
  have highValue : ‖weighted.ofLp.1.ofLp.1‖ ^ 2 ≤ ‖weighted‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr highBound
  simp only [coupledIncomingSquare,mul_add]
  have measurableHigh : Measurable (fun radius : ℝ => ENNReal.ofReal radius⁻¹ *
      highIncomingSquare lower length positive bounded field.ofLp.1.ofLp.1 radius) := by
    exact (measurable_inv.ennreal_ofReal).fun_mul
      (highIncomingSquare_measurable lower length positive bounded field.ofLp.1.ofLp.1)
  rw [lintegral_add_left measurableHigh (fun radius => ENNReal.ofReal radius⁻¹ *
    lowIncomingSquare lower length positive bounded field.ofLp.2 radius)]
  exact (add_le_add high low).trans
    ((add_le_add (ENNReal.ofReal_le_ofReal highValue) (ENNReal.ofReal_le_ofReal lowValue)).trans_eq
      (ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)).symm)

/-- The full density is literally the squared norm of the incoming trace of
the actual restricted field, retaining both high and low boundary blocks. -/
theorem coupledIncomingSquare_eq_restricted_norm
    (upper : ℝ) (upperPositive : 0 < upper) (upperBounded : upper < 1) (included : lower ≤ upper)
    (field : CoupledSpace lower length positive lengthPositive) :
    coupledIncomingSquare lower length positive (included.trans_lt upperBounded) lengthPositive field upper =
      ENNReal.ofReal (‖coupledIncomingTrace upper length upperPositive upperBounded lengthPositive
        (coupledEndpointRestriction lower upper length positive upperPositive upperBounded lengthPositive included field)‖ ^ 2) := by
  have high := highIncomingSquare_eq_restricted_norm lower upper length positive upperPositive upperBounded lengthPositive included field.ofLp.1.ofLp.1
  have low := lowIncomingSquare_eq_restricted_norm lower upper length positive upperPositive upperBounded included field.ofLp.2
  refine (congrArg₂ (fun first second : ℝ≥0∞ => first + second) high low).trans ?_
  rw [coupledIncomingTrace,WithLp.prod_norm_sq_eq_of_L2]
  exact (ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)).symm

end Grad.AnnularIncomingIntegrability
