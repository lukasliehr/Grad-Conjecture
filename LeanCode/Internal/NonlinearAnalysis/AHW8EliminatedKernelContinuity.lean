import AHW7LiteralCircularEliminationFormula

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularKernelContinuity

theorem radialNormalizedRetainedFirstRowKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) :
    RegularKernelFamily (radialNormalizedRetainedFirstRowKernel parameters L compact state) := by
  unfold radialNormalizedRetainedFirstRowKernel
  with_reducible repeat' first
    | exact radialNormalizedCovariantKernel_regular parameters L compact state
    | exact radialNormalizedRotatedCovariantKernel_regular parameters L compact state
    | exact radialRetainedForceKernel_regular parameters L compact state
    | apply RegularKernelFamily.comp
    | apply RegularKernelFamily.sub
  all_goals first
    | exact scalarModeRadialKernel_regular parameters _ _ _ _
    | exact constantMatrixRadialKernel_regular parameters _ _ _

theorem radialEliminationRightHandKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) :
    RegularKernelFamily (radialEliminationRightHandKernel parameters L compact state) := by
  unfold radialEliminationRightHandKernel
  exact (scalarModeRadialKernel_regular parameters _ _ _ _).comp
    (((constantMatrixRadialKernel_regular parameters _ _ _).sub
      ((radialNormalizedRetainedFirstRowKernel_regular parameters L compact state.val).comp
        (constantMatrixRadialKernel_regular parameters _ _ _))).sub
      (constantMatrixRadialKernel_regular parameters _ _ _))

theorem radialEliminatedXKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) :
    RegularKernelFamily (radialEliminatedXKernel parameters L compact state) :=
  (radialRetainedHighInverse_regular parameters L compact state).comp
    (radialEliminationRightHandKernel_regular parameters L compact state)

theorem radialEliminatedSevenKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) :
    RegularKernelFamily (radialEliminatedSevenKernel parameters L compact state) :=
  ((constantMatrixRadialKernel_regular parameters _ _ _).comp
    (radialEliminatedXKernel_regular parameters L compact state)).add
      (constantMatrixRadialKernel_regular parameters _ _ _)

theorem radialEliminatedXError_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) :
    RegularKernelFamily (fun r => fullKernelSub (radialEliminatedXKernel parameters L compact state r)
      (circularEliminatedXKernel (radialKernelParameters parameters r) L)) :=
  (radialEliminatedXKernel_regular parameters L compact state).sub
    (fixedRadialKernel_regular parameters _ (fun _ _ => sameCircularEliminatedXKernel _ _ L))

end Grad.AnnularReconstruction
