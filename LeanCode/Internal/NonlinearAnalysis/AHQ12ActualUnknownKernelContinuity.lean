import AHQ11ActualKnownKernelContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularKernelContinuity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularReconstruction

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact)

theorem radialUnknownNKernel_regular :
    RegularKernelFamily (fun r : RadialPoint => radialUnknownNKernel parameters L compact state.val r state.firstSmall) := by
  have i0 := fixedRadialKernel_regular parameters firstCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have i1 := fixedRadialKernel_regular parameters secondCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have i2 := fixedRadialKernel_regular parameters thirdCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have twice := fixedRadialKernel_regular parameters (fun p => fullKernelSmul 2 (fullIdentityKernel p 1)) (fun _ _ _ _ => rfl)
  have mean := fixedRadialKernel_regular parameters (fun p => angularMeanKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have free := fixedRadialKernel_regular parameters (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have qa := (radialGaugeQKernel_regular parameters L compact state.val state.gaugeSmall).comp
    (fixedRadialKernel_regular parameters actualUnknownQAKernel sameUnknownQAKernel)
  have f0 := radialForceKernel_regular parameters L compact state.val 0 0
  have f2 := radialForceKernel_regular parameters L compact state.val 1 0
  have rf0 := radialRotatedForceKernel_regular parameters L compact state.val 0 0
  exact (i0.comp (mean.comp (f0.comp qa)).neg).add
    ((i1.comp (twice.sub ((rf0.comp qa).add (f0.comp i0)))).add
      (i2.comp (free.comp (f2.comp qa)).neg))

theorem radialUnknownWKernel_regular :
    RegularKernelFamily (fun r : RadialPoint => radialUnknownWKernel parameters L compact state.val r state.firstSmall) :=
  (radialEncodedFirstInverseKernel_regular parameters L compact state.val state.firstSmall).comp
    (radialUnknownNKernel_regular parameters L compact state)

theorem radialUnknownUKernel_regular :
    RegularKernelFamily (fun r : RadialPoint => radialUnknownUKernel parameters L compact state.val r state.firstSmall) := by
  have j := fixedRadialKernel_regular parameters encodedJKernel sameEncodedJKernel
  have qa := fixedRadialKernel_regular parameters actualUnknownQAKernel sameUnknownQAKernel
  exact (radialGaugeQKernel_regular parameters L compact state.val state.gaugeSmall).comp
    ((j.comp (radialUnknownWKernel_regular parameters L compact state)).add qa)

theorem radialUnknownVKernel_regular :
    RegularKernelFamily (fun r : RadialPoint => radialUnknownVKernel parameters L compact state.val r state.firstSmall) := by
  have rotation := fixedRadialKernel_regular parameters encodedRotationKernel sameEncodedRotationKernel
  have i0 := fixedRadialKernel_regular parameters firstCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  exact (rotation.comp (radialUnknownWKernel_regular parameters L compact state)).add i0

end Grad.AnnularKernelContinuity
