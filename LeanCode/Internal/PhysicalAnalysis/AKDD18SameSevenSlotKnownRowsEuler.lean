import AKDD17ActualSigmaComponentEuler

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularRadialSmoothness
open OriginalEulerAssembly
attribute [local irreducible] fullKernelComposition fullKernelAdd fullKernelNeg fullKernelSmul polynomialKernelAction

/-- The actual normalized seven-slot source rows, including both original
force rows and the literal L-inverse factor in the third equation. -/
def originalKnownEncodedDataEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialKnownEncodedDataKernel parameters L compact state.val radius state.gaugeSmall) := by
  have qs := (originalGaugeQEulerFamily parameters L compact).comp
    ((second parameters L compact).comp (slot parameters L compact 3))
  have rqs := (second parameters L compact).comp (slot parameters L compact 1)
  have f0 := originalForceEulerFamily parameters L compact 0
  have f2 := originalForceEulerFamily parameters L compact 1
  have rf0 := originalRotatedForceEulerFamily parameters L compact 0
  unfold radialKnownEncodedDataKernel radialKnownD0Kernel radialKnownD1Kernel radialKnownD2Kernel
    radialKnownQStarKernel radialKnownRotatedQStarKernel
  exact ((first parameters L compact).comp
    (((mean parameters L compact 1).comp (slot parameters L compact 4)).sub
      ((mean parameters L compact 1).comp (f0.comp qs)))).add
    (((second parameters L compact).comp ((slot parameters L compact 5).sub
      ((free parameters L compact 1).comp ((rf0.comp qs).add (f0.comp rqs))))).add
    ((third parameters L compact).comp
      (((slot parameters L compact 6).add (scaledSlot parameters L compact 2)).sub
        ((free parameters L compact 1).comp (f2.comp qs)))))

def originalKnownWEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialKnownWKernel parameters L compact state.val radius state.firstSmall) :=
  (originalEncodedFirstInverseEulerFamily parameters L compact).comp (originalKnownEncodedDataEulerFamily parameters L compact)

def originalKnownAStarEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialKnownAStarKernel parameters L compact state.val radius state.firstSmall) :=
  (originalGaugeQEulerFamily parameters L compact).comp
    (((decoding parameters L compact).comp (originalKnownWEulerFamily parameters L compact)).add
      ((second parameters L compact).comp (slot parameters L compact 3)))

def originalKnownRAStarEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialKnownRAStarKernel parameters L compact state.val radius state.firstSmall) :=
  ((rotation parameters L compact).comp (originalKnownWEulerFamily parameters L compact)).add
    ((second parameters L compact).comp (slot parameters L compact 1))

/-- All four actual mass products remain present, including both kappa1
terms on normalized scalar and rotated-scalar slots. -/
def originalKnownJStarEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialKnownJStarKernel parameters L compact state.val radius state.firstSmall) :=
  (free parameters L compact 1).comp
    ((((originalRotatedSigmaEulerFamily parameters L compact).comp (originalKnownAStarEulerFamily parameters L compact)).add
      ((originalSigmaEulerFamily parameters L compact).comp (originalKnownRAStarEulerFamily parameters L compact))).add
    (((originalRotatedSigmaComponentEulerFamily parameters L compact 1).comp (slot parameters L compact 3)).add
      ((originalSigmaComponentEulerFamily parameters L compact 1).comp (slot parameters L compact 1))))

end Grad.OriginalCartesianTameEstimate
