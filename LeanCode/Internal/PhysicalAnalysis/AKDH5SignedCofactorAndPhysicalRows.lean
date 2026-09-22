import AKDH4ActualRetainedForceEuler

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction
open OriginalEulerAssembly

attribute [local irreducible] fullKernelComposition fullKernelAdd fullKernelNeg fullKernelSmul

def ActualEulerFamily.congr {parameters : PhaseParameters} {L compact : ℝ} {source target : ℕ}
    {first second : (state : AnnularReconstructionState parameters L compact) →
      (radius : RadialPoint) → RadialKernel parameters radius source target}
    (family : ActualEulerFamily parameters L compact first)
    (same : ∀ state radius, first state radius = second state radius) :
    ActualEulerFamily parameters L compact second where
  kernels := family.kernels
  zero state radius := (family.zero state radius).trans (same state radius)
  derivative := family.derivative
  moments := family.moments

def originalSignedCofactorRowEulerFamily (parameters : PhaseParameters) (L compact : ℝ) (row : Fin 3) :=
  (ActualEulerFamily.fixed parameters L compact
    (fun phase => fullKernelNeg (coordinateProjectionKernel phase 3 row))
    (fun p q => (sameConstantMatrixKernel p q _ _ _).neg)).add
    (actualCofactorRowEulerFamily parameters L compact row 0 0)

def originalSignedCofactorComponentEulerFamily (parameters : PhaseParameters) (L compact : ℝ) (row column : Fin 3) :=
  (ActualEulerFamily.fixed parameters L compact (fun phase => circularCofactorComponentKernel phase row column)
    (fun p q => sameCircularCofactorComponentKernel p q row column)).add
    (actualCofactorComponentEulerFamily parameters L compact row column 0 0)

def originalForceZeroEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :=
  (ActualEulerFamily.fixed parameters L compact
    (fun phase => fullKernelSmul (-2) (coordinateProjectionKernel phase 3 0))
    (fun p q => (sameConstantMatrixKernel p q _ _ _).smul (-2))).add
    (originalForceEulerFamily parameters L compact 0)

def originalKVEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :=
  (((actualCofactorRowEulerFamily parameters L compact 1 0 1).add
    ((originalSignedCofactorComponentEulerFamily parameters L compact 1 0).comp
      ((free parameters L compact 1).comp (actualRetainedForceEulerFamily parameters L compact)))).add
    ((originalSignedCofactorComponentEulerFamily parameters L compact 1 1).comp
      (originalForceZeroEulerFamily parameters L compact))).sub
    ((originalSignedCofactorComponentEulerFamily parameters L compact 1 2).comp
      ((free parameters L compact 1).comp (originalForceEulerFamily parameters L compact 1)))

def originalPhysicalFirstRowEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :=
  ((ActualEulerFamily.fixed parameters L compact (fun phase => coordinateProjectionKernel phase 3 0)
    (fun p q => sameConstantMatrixKernel p q _ _ _)).comp
    (originalNormalizedRotatedCovariantEulerFamily parameters L compact)).sub
    ((actualRetainedForceEulerFamily parameters L compact).comp
      (originalNormalizedCovariantEulerFamily parameters L compact))

def originalPhysicalCEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :=
  ((((actualCofactorRowEulerFamily parameters L compact 2 0 1).comp
    (originalNormalizedCovariantEulerFamily parameters L compact)).add
    ((originalSignedCofactorRowEulerFamily parameters L compact 2).comp
      (originalNormalizedRotatedCovariantEulerFamily parameters L compact))).add
    ((actualCofactorComponentEulerFamily parameters L compact 1 2 0 1).comp
      (slot parameters L compact 3))).add
    ((originalSignedCofactorComponentEulerFamily parameters L compact 1 2).comp
      (slot parameters L compact 1))

theorem originalPhysicalFirstRowEulerFamily_same (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (radius : RadialPoint) :
    (originalPhysicalFirstRowEulerFamily parameters L compact).kernels state.val 0 radius =
      radialNormalizedUnprojectedFirstRowKernel parameters L compact state radius := by
  rw [(originalPhysicalFirstRowEulerFamily parameters L compact).zero]
  rfl

theorem originalPhysicalCEulerFamily_same (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (radius : RadialPoint) :
    (originalPhysicalCEulerFamily parameters L compact).kernels state.val 0 radius =
      radialNormalizedUnprojectedCKernel parameters L compact state radius := by
  rw [(originalPhysicalCEulerFamily parameters L compact).zero]
  rfl

end Grad.OriginalCartesianTameEstimate
