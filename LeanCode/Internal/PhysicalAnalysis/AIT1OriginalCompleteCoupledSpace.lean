import AEM99OriginalCrossMapConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCoupledInverse
open Grad.AnnularCrossMaps Grad.AnnularLowEnergy Grad.AnnularOmegaGraph Grad.AnnularVariational

/-- Literal BF2 Hilbert sum. Its low component is the original rho graph,
with no extra radial tilt or independent endpoint coordinate. -/
abbrev CoupledSpace (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :=
  WithLp 2 (CrossHighSpace lower length positive lengthPositive × lowEnergyGraph lower length positive)

theorem coupledSpace_complete (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    CompleteSpace (CoupledSpace lower length positive lengthPositive) := inferInstance

def coupledHigh (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    CoupledSpace lower length positive lengthPositive →L[ℂ] CrossHighSpace lower length positive lengthPositive :=
  (ContinuousLinearMap.fst ℂ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).toContinuousLinearMap

def coupledLow (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    CoupledSpace lower length positive lengthPositive →L[ℂ] lowEnergyGraph lower length positive :=
  (ContinuousLinearMap.snd ℂ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).toContinuousLinearMap

theorem coupledSpace_norm_sq (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive) :
    ‖field‖ ^ 2 = ‖coupledHigh lower length positive lengthPositive field‖ ^ 2 +
      ‖coupledLow lower length positive lengthPositive field‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 field

theorem coupledSpace_original_graph_norm_sq (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive) :
    ‖field‖ ^ 2 = ‖field.ofLp.1.ofLp.1‖ ^ 2 +
      (‖field.ofLp.1.ofLp.2.val 0‖ ^ 2 + ‖field.ofLp.1.ofLp.2.val 1‖ ^ 2) +
      (‖field.ofLp.2.val 0‖ ^ 2 + ‖field.ofLp.2.val 1‖ ^ 2) := by
  have outer := WithLp.prod_norm_sq_eq_of_L2 field
  have high := WithLp.prod_norm_sq_eq_of_L2 field.ofLp.1
  change ‖field‖ ^ 2 = ‖field.ofLp.1‖ ^ 2 + ‖field.ofLp.2‖ ^ 2 at outer
  change ‖field.ofLp.1‖ ^ 2 = ‖field.ofLp.1.ofLp.1‖ ^ 2 + ‖field.ofLp.1.ofLp.2‖ ^ 2 at high
  rw [outer, high, annularOmegaGraph_norm_sq lower length positive lengthPositive,
    lowEnergyGraph_norm_sq lower length positive]

theorem coupledHigh_bound (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive) :
    ‖coupledHigh lower length positive lengthPositive field‖ ≤ ‖field‖ := by
  have square := coupledSpace_norm_sq lower length positive lengthPositive field
  nlinarith [norm_nonneg field, norm_nonneg (coupledHigh lower length positive lengthPositive field),
    sq_nonneg ‖coupledLow lower length positive lengthPositive field‖]

theorem coupledLow_bound (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive) :
    ‖coupledLow lower length positive lengthPositive field‖ ≤ ‖field‖ := by
  have square := coupledSpace_norm_sq lower length positive lengthPositive field
  nlinarith [norm_nonneg field, norm_nonneg (coupledLow lower length positive lengthPositive field),
    sq_nonneg ‖coupledHigh lower length positive lengthPositive field‖]

end Grad.AnnularCoupledInverse
