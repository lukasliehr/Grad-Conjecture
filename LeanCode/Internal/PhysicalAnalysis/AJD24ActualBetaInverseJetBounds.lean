import AJD2ActualBoundaryInverseOrbit
import BCI16InverseReferenceMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.AnnularReconstruction Grad.AnnularKernelOrbit Grad.GaugeCoefficients.Physical.Allocation

private theorem highAngularKernel_zeroShift (parameters : PhaseParameters) :
    ZeroShiftKernel (highAngularKernel parameters 1) := by
  intro shift nonzero input
  simp only [highAngularKernel, scalarModeDiagonalKernel, modeDiagonalKernel_entry, if_neg nonzero]

private theorem negativeHighAngularKernel_zeroShift (parameters : PhaseParameters) :
    ZeroShiftKernel (fullKernelNeg (highAngularKernel parameters 1)) := by
  intro shift nonzero input
  rw [fullKernelNeg_entry, highAngularKernel_zeroShift parameters shift nonzero input, neg_zero]

/-- Positive jets of the actual beta inverse contain only its deviation from
-Q. The original negative-half moment costs one derivative, hence B_(8+j). -/
theorem actualBoundaryInverseOrbitJet_positive_oneHigh (parameters : PhaseParameters) (L compact : ℝ)
    (angular cell : ℕ) (orderPositive : 0 < angular + cell) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (state : RetainedInverseState parameters L compact) (tau : OrbitParameter),
      ‖actualBoundaryInverseOrbitJet parameters L compact state angular cell tau‖ ≤
        constant * physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (8 + (angular + cell)) := by
  obtain ⟨constant, nonnegative, bound⟩ := actualHighBoundaryInverse_referenceMoments parameters L compact (1 + (angular + cell))
  refine ⟨constant, nonnegative, ?_⟩
  intro state tau
  let kernel := actualHighBoundaryInverse state.outerInverseState.val state.outerInverseState.property
  have referenceDifference : fullKernelSub kernel (fullKernelNeg (highAngularKernel parameters 1)) =
      fullKernelAdd kernel (highAngularKernel parameters 1) := by
    apply FullTwoFrequencyKernel.ext_entry
    intro shift input
    simp only [fullKernelSub_entry, fullKernelNeg_entry, fullKernelAdd_entry, sub_neg_eq_add]
  have same : boundaryOrbitJetAction parameters 0 0 kernel tau angular cell =
      boundaryOrbitJetAction parameters 0 0 (fullKernelAdd kernel (highAngularKernel parameters 1)) tau angular cell := by
    unfold boundaryOrbitJetAction
    rw [kernelOrbitJet_referenceDifference tau angular cell orderPositive kernel
      (fullKernelNeg (highAngularKernel parameters 1)) (negativeHighAngularKernel_zeroShift parameters), referenceDifference]
  have action := boundaryOrbitJetAction_norm_le parameters 0 0 (fullKernelAdd kernel (highAngularKernel parameters 1)) tau angular cell
  have moment := bound state.outerInverseState
  have whole : ‖boundaryOrbitJetAction parameters 0 0 kernel tau angular cell‖ ≤
      constant * physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (8 + (angular + cell)) := by
    rw [same]
    change fullKernelMoment parameters (1 + (angular + cell)) (fullKernelAdd kernel (highAngularKernel parameters 1)) ≤
      constant * physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (1 + (angular + cell) + 7) at moment
    exact action.trans (by simpa only [show 1 + (angular + cell) + 7 = 8 + (angular + cell) by omega] using moment)
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg nonnegative (physicalBudget_nonnegative _ _ _ _ _))
  intro datum
  exact ((boundaryOrbitJetAction parameters 0 0 kernel tau angular cell).le_opNorm datum.val).trans
    (mul_le_mul_of_nonneg_right whole (norm_nonneg datum))

/-- The zeroth actual beta inverse remains uniformly bounded on B8≤1. -/
theorem actualBoundaryInverseOrbit_zero_uniform (parameters : PhaseParameters) (L compact : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (state : RetainedInverseState parameters L compact)
      (_small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ 1) (tau : OrbitParameter),
      ‖actualBoundaryInverseOrbitJet parameters L compact state 0 0 tau‖ ≤ constant := by
  obtain ⟨constant, nonnegative, bound⟩ := actualHighBoundaryInverse_physicalMoments parameters L compact 1
  refine ⟨2 * constant, by positivity, ?_⟩
  intro state small tau
  have moment := bound state.outerInverseState
  have size : state.outerInverseState.val.val.size 1 ≤ 2 := by
    change 1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ 2
    linarith
  have action := boundaryOrbitJetAction_norm_le parameters 0 0
    (actualHighBoundaryInverse state.outerInverseState.val state.outerInverseState.property) tau 0 0
  have whole : ‖boundaryOrbitJetAction parameters 0 0
      (actualHighBoundaryInverse state.outerInverseState.val state.outerInverseState.property) tau 0 0‖ ≤ 2 * constant := by
    apply action.trans
    exact moment.trans ((mul_le_mul_of_nonneg_left size nonnegative).trans_eq (mul_comm constant 2))
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro datum
  exact ((boundaryOrbitJetAction parameters 0 0
    (actualHighBoundaryInverse state.outerInverseState.val state.outerInverseState.property) tau 0 0).le_opNorm datum.val).trans
      (mul_le_mul_of_nonneg_right whole (norm_nonneg datum))

end Grad.AnnularCrossOrbit
