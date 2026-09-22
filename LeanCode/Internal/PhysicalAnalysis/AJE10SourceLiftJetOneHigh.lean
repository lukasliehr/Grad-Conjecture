import AJE9ActualSourceBoundaryLiftOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularKernelOrbit Grad.AnnularCurrentSource Grad.BoundaryKernelAction
open Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse

variable (parameters : PhaseParameters) (traceAngular traceCell : ℕ)

theorem graphSourceBoundaryVectorMap_norm :
    ‖graphSourceBoundaryVectorMap parameters traceAngular traceCell‖ ≤
      fullKernelMoment parameters (traceAngular + traceCell + 1) (sourceTupleProjectionKernel parameters) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (fullKernelMoment_nonnegative parameters _ _)
  intro source
  rw [graphSourceBoundaryVectorMap_apply]
  exact graphSourceBoundaryVector_bound parameters traceAngular traceCell source

variable (L compact : ℝ) (angular cell : ℕ)

/-- State-independent moment constant for the actual source lift jet. -/
def sourceLiftJetConstant : ℝ :=
  graphSourceLiftMomentConstant parameters L compact (traceAngular + traceCell + 1 + (angular + cell)) *
    fullKernelMoment parameters (traceAngular + traceCell + 1) (sourceTupleProjectionKernel parameters)

theorem sourceLiftJetConstant_nonnegative :
    0 ≤ sourceLiftJetConstant parameters traceAngular traceCell L compact angular cell :=
  mul_nonneg (graphSourceLiftMomentConstant_nonnegative parameters L compact _)
    (fullKernelMoment_nonnegative parameters _ _)

/-- Only one original primitive budget enters each source lift jet. At
base trace grade its size index is j+1, hence the original B_(j+8). -/
theorem graphSourceLiftOrbitJet_oneHigh (state : BoundaryInverseState parameters L compact) (tau : OrbitParameter) :
    ‖graphSourceLiftOrbitJet parameters L compact state traceAngular traceCell angular cell tau‖ ≤
      sourceLiftJetConstant parameters traceAngular traceCell L compact angular cell *
        state.val.val.size (traceAngular + traceCell + 1 + (angular + cell)) := by
  have kernelBound := (boundaryOrbitJetAction_norm_le parameters traceAngular traceCell
    (actualSourceBoundaryLiftKernel state) tau angular cell).trans
      (graphSourceLiftMomentConstant_bound parameters L compact (traceAngular + traceCell + 1 + (angular + cell)) state)
  have projectionBound := graphSourceBoundaryVectorMap_norm parameters traceAngular traceCell
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul kernelBound projectionBound (norm_nonneg _)
      (mul_nonneg (graphSourceLiftMomentConstant_nonnegative parameters L compact _) (state.val.val.size_nonnegative _))).trans_eq
      (by unfold sourceLiftJetConstant; ring))

theorem graphSourceLiftOrbitJet_apply_oneHigh (state : BoundaryInverseState parameters L compact)
    (tau : OrbitParameter) (source : SourceBoundaryTuple) :
    ‖graphSourceLiftOrbitJet parameters L compact state traceAngular traceCell angular cell tau source‖ ≤
      sourceLiftJetConstant parameters traceAngular traceCell L compact angular cell *
        state.val.val.size (traceAngular + traceCell + 1 + (angular + cell)) * ‖source‖ :=
  ((graphSourceLiftOrbitJet parameters L compact state traceAngular traceCell angular cell tau).le_opNorm source).trans
    (mul_le_mul_of_nonneg_right
      (graphSourceLiftOrbitJet_oneHigh parameters traceAngular traceCell L compact angular cell state tau) (norm_nonneg source))

end Grad.AnnularStrongOrbit
