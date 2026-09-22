import AKDH5SignedCofactorAndPhysicalRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction
open OriginalEulerAssembly
attribute [local irreducible] fullKernelComposition fullKernelAdd fullKernelNeg fullKernelSmul

theorem fullKernelComposition_smul_outer {parameters : PhaseParameters} {source middle target : ℕ}
    (scalar : ℂ) (outer : FullTwoFrequencyKernel parameters middle target)
    (inner : FullTwoFrequencyKernel parameters source middle) :
    fullKernelComposition (fullKernelSmul scalar outer) inner = fullKernelSmul scalar (fullKernelComposition outer inner) := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift input
  simp only [fullKernelComposition_entry,fullKernelSmul_entry,ContinuousLinearMap.smul_comp,tsum_const_smul'']

def ActualEulerFamily.radius {parameters : PhaseParameters} {L compact : ℝ} {source target : ℕ}
    {base : (state : AnnularReconstructionState parameters L compact) →
      (radius : RadialPoint) → RadialKernel parameters radius source target}
    (family : ActualEulerFamily parameters L compact base) :
    ActualEulerFamily parameters L compact (fun state radius => fullKernelSmul (radius.val : ℂ) (base state radius)) :=
  ((fixedRadiusEulerFamily parameters L compact (fun phase => fullIdentityKernel phase target)
    (fun p q => sameFullIdentityKernel p q target)).comp family).congr
      (fun state radius => by rw [fullKernelComposition_smul_outer,fullIdentityKernel_comp_rect])

/-- The exact original unprojected rV row. Both explicit radius factors
are differentiated as D(r)=r and keep their original negative signs. -/
def originalPhysicalRVRawEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :=
  ((((originalSignedCofactorComponentEulerFamily parameters L compact 1 1).comp
    (slot parameters L compact 1)).add
    ((originalKVEulerFamily parameters L compact).comp
      (originalNormalizedCovariantEulerFamily parameters L compact))).sub
    (((actualCofactorComponentEulerFamily parameters L compact 1 0 1 0).comp
      (slot parameters L compact 3)).radius)).sub
    ((((actualCofactorComponentEulerFamily parameters L compact 1 2 0 2).comp
      (slot parameters L compact 3)).radius).smul (L : ℂ)⁻¹)

def originalPhysicalRVEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :=
  (free parameters L compact 1).comp (originalPhysicalRVRawEulerFamily parameters L compact)

theorem originalPhysicalRVRawEulerFamily_same (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (radius : RadialPoint) :
    (originalPhysicalRVRawEulerFamily parameters L compact).kernels state.val 0 radius =
      radialNormalizedUnprojectedRVKernel parameters L compact state radius := by
  rw [(originalPhysicalRVRawEulerFamily parameters L compact).zero]
  apply congrArg₂ fullKernelSub rfl
  apply FullTwoFrequencyKernel.ext_entry
  intro shift input
  simp only [fullKernelSmul_entry,smul_smul,mul_comm]
  rfl

theorem originalPhysicalRVEulerFamily_same (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (radius : RadialPoint) :
    (originalPhysicalRVEulerFamily parameters L compact).kernels state.val 0 radius =
      radialNormalizedPhysicalRVKernel parameters L compact state radius := by
  rw [(originalPhysicalRVEulerFamily parameters L compact).zero]
  apply congrArg (fullKernelComposition (angularMeanFreeKernel (radialKernelParameters parameters radius) 1))
  exact (originalPhysicalRVRawEulerFamily parameters L compact).zero state.val radius ▸
    originalPhysicalRVRawEulerFamily_same parameters L compact state radius

end Grad.OriginalCartesianTameEstimate
