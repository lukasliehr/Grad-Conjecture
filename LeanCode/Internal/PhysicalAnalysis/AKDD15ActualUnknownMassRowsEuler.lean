import AKDD14SameEncodedFirstInverseEuler

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularRadialSmoothness
open OriginalEulerAssembly
attribute [local irreducible] fullKernelComposition fullKernelAdd fullKernelNeg fullKernelSmul polynomialKernelAction

def originalUnknownNEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialUnknownNKernel parameters L compact state.val radius state.firstSmall) := by
  have qa := (originalGaugeQEulerFamily parameters L compact).comp (unknown parameters L compact)
  have f0 := originalForceEulerFamily parameters L compact 0
  have f2 := originalForceEulerFamily parameters L compact 1
  have rf0 := originalRotatedForceEulerFamily parameters L compact 0
  unfold radialUnknownNKernel radialUnknownN0Kernel radialUnknownN1Kernel radialUnknownN2Kernel radialUnknownGaugeQAKernel
  exact ((first parameters L compact).comp ((mean parameters L compact 1).comp (f0.comp qa)).neg).add
    (((second parameters L compact).comp ((twice parameters L compact 1).sub
      ((rf0.comp qa).add (f0.comp (first parameters L compact))))).add
      ((third parameters L compact).comp ((free parameters L compact 1).comp (f2.comp qa)).neg))

def originalUnknownWEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialUnknownWKernel parameters L compact state.val radius state.firstSmall) :=
  (originalEncodedFirstInverseEulerFamily parameters L compact).comp (originalUnknownNEulerFamily parameters L compact)

def originalUnknownUEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialUnknownUKernel parameters L compact state.val radius state.firstSmall) :=
  (originalGaugeQEulerFamily parameters L compact).comp
    (((decoding parameters L compact).comp (originalUnknownWEulerFamily parameters L compact)).add (unknown parameters L compact))

def originalUnknownVEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialUnknownVKernel parameters L compact state.val radius state.firstSmall) :=
  ((rotation parameters L compact).comp (originalUnknownWEulerFamily parameters L compact)).add (first parameters L compact)

def originalMassPerturbationEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialMassPerturbationKernel parameters L compact state.val radius state.firstSmall) :=
  (free parameters L compact 1).comp
    (((originalRotatedSigmaEulerFamily parameters L compact).comp (originalUnknownUEulerFamily parameters L compact)).add
      ((originalSigmaEulerFamily parameters L compact).comp (originalUnknownVEulerFamily parameters L compact)))

end Grad.OriginalCartesianTameEstimate
