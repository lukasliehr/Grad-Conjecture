import AHQ10ActualSigmaKernelContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularKernelContinuity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact)

theorem radialKnownEncodedDataKernel_regular :
    RegularKernelFamily (fun r : RadialPoint => radialKnownEncodedDataKernel parameters L compact state.val r state.gaugeSmall) := by
  have i0 := fixedRadialKernel_regular parameters firstCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have i1 := fixedRadialKernel_regular parameters secondCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have i2 := fixedRadialKernel_regular parameters thirdCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have slot (component : Fin 7) := fixedRadialKernel_regular parameters (fun p => sevenInputSlotKernel p component) (fun p q => sameConstantMatrixKernel p q _ _ _)
  have scaledSlot := fixedRadialKernel_regular parameters
    (fun p => fullKernelSmul (L : ℂ)⁻¹ (sevenInputSlotKernel p 2))
    (fun _ _ _ _ => rfl)
  have mean := fixedRadialKernel_regular parameters (fun p => angularMeanKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have free := fixedRadialKernel_regular parameters (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have qstar := (radialGaugeQKernel_regular parameters L compact state.val state.gaugeSmall).comp (i1.comp (slot 3))
  have rqstar := i1.comp (slot 1)
  have f0 := radialForceKernel_regular parameters L compact state.val 0 0
  have f2 := radialForceKernel_regular parameters L compact state.val 1 0
  have rf0 := radialRotatedForceKernel_regular parameters L compact state.val 0 0
  exact (i0.comp ((mean.comp (slot 4)).sub (mean.comp (f0.comp qstar)))).add
    ((i1.comp ((slot 5).sub (free.comp ((rf0.comp qstar).add (f0.comp rqstar))))).add
      (i2.comp (((slot 6).add scaledSlot).sub (free.comp (f2.comp qstar)))))

theorem radialKnownWKernel_regular :
    RegularKernelFamily (fun r : RadialPoint => radialKnownWKernel parameters L compact state.val r state.firstSmall) :=
  (radialEncodedFirstInverseKernel_regular parameters L compact state.val state.firstSmall).comp
    (radialKnownEncodedDataKernel_regular parameters L compact state)

theorem radialKnownAStarKernel_regular :
    RegularKernelFamily (fun r : RadialPoint => radialKnownAStarKernel parameters L compact state.val r state.firstSmall) := by
  have j := fixedRadialKernel_regular parameters encodedJKernel sameEncodedJKernel
  have i1 := fixedRadialKernel_regular parameters secondCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have slot := fixedRadialKernel_regular parameters (fun p => sevenInputSlotKernel p 3) (fun p q => sameConstantMatrixKernel p q _ _ _)
  exact (radialGaugeQKernel_regular parameters L compact state.val state.gaugeSmall).comp
    ((j.comp (radialKnownWKernel_regular parameters L compact state)).add (i1.comp slot))

theorem radialKnownRAStarKernel_regular :
    RegularKernelFamily (fun r : RadialPoint => radialKnownRAStarKernel parameters L compact state.val r state.firstSmall) := by
  have rotation := fixedRadialKernel_regular parameters encodedRotationKernel sameEncodedRotationKernel
  have i1 := fixedRadialKernel_regular parameters secondCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have slot := fixedRadialKernel_regular parameters (fun p => sevenInputSlotKernel p 1) (fun p q => sameConstantMatrixKernel p q _ _ _)
  exact (rotation.comp (radialKnownWKernel_regular parameters L compact state)).add (i1.comp slot)

end Grad.AnnularKernelContinuity
