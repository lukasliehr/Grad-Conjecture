import AKDD12RotatedPrimitiveEulerFamilies

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.Allocation

def originalForceEulerFamily (parameters : PhaseParameters) (L compact : ℝ) (kind : Fin 2) :
    ActualEulerFamily parameters L compact (fun state radius => radialForceKernel parameters L compact state.val radius kind 0) where
  kernels state rank radius := actualForceEulerKernel parameters L compact state.val kind radius rank
  zero _ _ := rfl
  derivative state lower positive bounded := actualForceEulerKernel_derivativeTower parameters L compact state.val kind lower positive bounded
  moments := by
    intro rank moment
    refine ⟨actualForceEulerMomentConstant parameters L kind moment rank,
      actualForceEulerMomentConstant_nonnegative parameters L kind moment rank,?_⟩
    intro state _ radius
    apply (actualForceEulerKernel_moment_bound parameters L compact kind rank moment state.val radius).trans
    apply mul_le_mul_of_nonneg_left _ (actualForceEulerMomentConstant_nonnegative parameters L kind moment rank)
    exact (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by omega : moment+rank+6 ≤ 10+(rank+moment))).trans (by linarith)

def originalSigmaEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact (fun state radius => radialSigmaKernel parameters L compact state.val radius 0) where
  kernels state rank radius := actualSigmaEulerKernel parameters L compact state.val radius rank
  zero _ _ := rfl
  derivative state lower positive bounded := actualSigmaEulerKernel_derivativeTower parameters L compact state.val lower positive bounded
  moments := by
    intro rank moment
    refine ⟨actualSigmaEulerMomentConstant parameters L moment rank,
      actualSigmaEulerMomentConstant_nonnegative parameters L moment rank,?_⟩
    intro state _ radius
    apply (actualSigmaEulerKernel_moment_bound parameters L compact rank moment state.val radius).trans
    apply mul_le_mul_of_nonneg_left _ (actualSigmaEulerMomentConstant_nonnegative parameters L moment rank)
    exact (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by omega : moment+rank+5 ≤ 10+(rank+moment))).trans (by linarith)

def originalGaugeQEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact (fun state radius => radialGaugeQKernel parameters L compact state.val radius state.gaugeSmall) where
  kernels := originalGaugeQEulerKernel parameters L compact
  zero := originalGaugeQEulerKernel_zero parameters L compact
  derivative := originalGaugeQEulerKernel_derivativeTower parameters L compact
  moments := originalGaugeQEulerKernel_originalMoments parameters L compact

namespace OriginalEulerAssembly
variable (parameters : PhaseParameters) (L compact : ℝ)

def first := ActualEulerFamily.fixed parameters L compact firstCoordinateInjectionKernel
  (fun p q => sameConstantMatrixKernel p q _ _ _)
def second := ActualEulerFamily.fixed parameters L compact secondCoordinateInjectionKernel
  (fun p q => sameConstantMatrixKernel p q _ _ _)
def third := ActualEulerFamily.fixed parameters L compact thirdCoordinateInjectionKernel
  (fun p q => sameConstantMatrixKernel p q _ _ _)
def decoding := ActualEulerFamily.fixed parameters L compact encodedJKernel sameEncodedJKernel
def rotation := ActualEulerFamily.fixed parameters L compact encodedRotationKernel sameEncodedRotationKernel
def unknown := ActualEulerFamily.fixed parameters L compact actualUnknownQAKernel sameUnknownQAKernel
def preconditioner := ActualEulerFamily.fixed parameters L compact encodedD0InverseKernel
  (fun p q => sameConstantMatrixKernel p q _ _ _)
def mean (dimension : ℕ) := ActualEulerFamily.fixed parameters L compact (fun p => angularMeanKernel p dimension)
  (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
def free (dimension : ℕ) := ActualEulerFamily.fixed parameters L compact (fun p => angularMeanFreeKernel p dimension)
  (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
def slot (index : Fin 7) := ActualEulerFamily.fixed parameters L compact (fun p => sevenInputSlotKernel p index)
  (fun p q => sameConstantMatrixKernel p q _ _ _)
def twice (dimension : ℕ) := ActualEulerFamily.fixed parameters L compact (fun p => fullKernelSmul 2 (fullIdentityKernel p dimension))
  (fun p q => (sameFullIdentityKernel p q dimension).smul _)
def scaledSlot (index : Fin 7) := ActualEulerFamily.fixed parameters L compact (fun p => fullKernelSmul (L : ℂ)⁻¹ (sevenInputSlotKernel p index))
  (fun p q => (sameConstantMatrixKernel p q _ _ _).smul _)

end OriginalEulerAssembly
end Grad.OriginalCartesianTameEstimate
