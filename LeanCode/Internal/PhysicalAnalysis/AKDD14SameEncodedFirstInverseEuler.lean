import AKDD13OriginalPrimitiveAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularRadialSmoothness
open OriginalEulerAssembly
attribute [local irreducible] fullKernelComposition fullKernelAdd fullKernelNeg fullKernelSmul polynomialKernelAction

def originalEncodedPerturbationEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialEncodedPerturbationKernel parameters L compact state.val radius state.gaugeSmall) := by
  have qj := (originalGaugeQEulerFamily parameters L compact).comp (decoding parameters L compact)
  have f0 := originalForceEulerFamily parameters L compact 0
  have f2 := originalForceEulerFamily parameters L compact 1
  have rf0 := originalRotatedForceEulerFamily parameters L compact 0
  unfold radialEncodedPerturbationKernel radialEncodedE0Kernel radialEncodedE1Kernel radialEncodedE2Kernel radialGaugeDecodedKernel
  exact ((first parameters L compact).comp ((mean parameters L compact 1).comp (f0.comp qj))).add
    (((second parameters L compact).comp ((free parameters L compact 1).comp
      ((rf0.comp qj).add (f0.comp (rotation parameters L compact))))).add
      ((third parameters L compact).comp ((free parameters L compact 1).comp (f2.comp qj))))

def originalPreconditionedEncodedEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialPreconditionedEncodedKernel parameters L compact state.val radius state.gaugeSmall) :=
  (preconditioner parameters L compact).comp (originalEncodedPerturbationEulerFamily parameters L compact)

/-- The existing encoded first inverse, with its actual sign and fixed
preconditioner. Its Euler words use the accepted original base inverse. -/
def originalEncodedFirstInverseEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialEncodedFirstInverseKernel parameters L compact state.val radius state.firstSmall) := by
  have inverse := (originalPreconditionedEncodedEulerFamily parameters L compact).neg.negativeInverse
    (fun state lower positive bounded => (radialPreconditionedEncodedKernel_smooth parameters L compact state.val lower positive bounded state.gaugeSmall).neg)
    (1/2) (by norm_num)
    (fun state radius => radialPreconditionedEncodedKernel_small parameters L compact state.val radius state.firstSmall)
    (by
      apply UniformRadialKernelMoments.negativeIdentityInverse (fun state => state.val.one_le_size)
      exact (radialPreconditionedEncodedKernel_physicalMoments parameters L compact).neg)
  exact inverse.neg.comp (preconditioner parameters L compact)

end Grad.OriginalCartesianTameEstimate
