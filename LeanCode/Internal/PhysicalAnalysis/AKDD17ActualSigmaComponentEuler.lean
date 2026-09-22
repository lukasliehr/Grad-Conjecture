import AKDD16SameMassInverseEuler

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularRadialSmoothness Grad.AnnularKernelContinuity
open Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualCurrentPrimitives

/-- Internal scalar-jet constructor for the two actual kappa1 terms in
the complete normalized mass right-hand side. -/
def scalarPrimitiveEulerFamily (parameters : PhaseParameters) (L compact : ℝ)
    (coefficients : AnnularReconstructionState parameters L compact → ℕ → ℝ → (ℤ × ℤ) → ℂ)
    (derivative : ∀ state raw point shift, HasDerivAt (fun radius => coefficients state raw radius shift)
      (coefficients state (raw+1) point shift) point)
    (summable : ∀ state raw (radius : RadialPoint) moment,
      Summable (productMoment parameters moment radius.val (coefficients state raw radius.val)))
    (cost : ℕ) (costBound : cost ≤ 10) (constants : ℕ → ℕ → ℝ)
    (nonnegative : ∀ raw moment, 0 ≤ constants raw moment)
    (bounds : ∀ state raw (radius : RadialPoint) moment,
      (∑' shift, productMoment parameters moment radius.val (coefficients state raw radius.val) shift) ≤
        constants raw moment * physicalBudget parameters state.val.field state.val.rho state.val.epsilon (moment+raw+cost)) :
    ActualEulerFamily parameters L compact (fun state radius =>
      radialScalarKernel parameters radius 1 (coefficients state 0 radius.val) (summable state 0 radius)) := by
  let kernels := fun (state : AnnularReconstructionState parameters L compact) (raw : ℕ) (radius : RadialPoint) =>
    radialScalarKernel parameters radius 1 (coefficients state raw radius.val) (summable state raw radius)
  have momentBound (state : AnnularReconstructionState parameters L compact) (raw moment : ℕ) (radius : RadialPoint) :
      fullKernelMoment (radialKernelParameters parameters radius) moment (kernels state raw radius) ≤
        (Real.exp (parameters.sigma0+2*parameters.gamma)*constants raw moment) *
          physicalBudget parameters state.val.field state.val.rho state.val.epsilon (moment+raw+cost) := by
    apply (radialScalarKernel_moment_le parameters radius 1 moment _ _).trans
    exact (mul_le_mul_of_nonneg_left (bounds state raw radius moment) (Real.exp_pos _).le).trans_eq (mul_assoc _ _ _).symm
  have regular (state : AnnularReconstructionState parameters L compact) (raw : ℕ) :
      RegularKernelFamily (kernels state raw) := by
    refine regularKernelFamily_of_bound _ ?_ _ (fun moment radius => momentBound state raw moment radius)
    intro shift input
    have continuousCoefficient : Continuous (fun point => coefficients state raw point shift) :=
      continuous_iff_continuousAt.mpr (fun point => (derivative state raw point shift).continuousAt)
    exact (continuousCoefficient.comp continuous_subtype_val).smul continuous_const
  refine ⟨(fun state rank radius => actualRawEulerKernel radius (fun raw => kernels state raw radius) rank),
    (fun _ _ => rfl),?_,?_⟩
  · intro state lower positive bounded
    apply actualRawEulerKernel_derivativeTower
    intro raw radius inside
    apply actualMatrixKernelAction_hasDerivWithinAt parameters lower positive bounded (kernels state)
      (fun raw point shift => scalarMultiplicationEntry 1 (coefficients state raw point) shift (0,0))
      (fun _ _ _ _ => rfl) _ (regular state) raw radius inside
    intro raw shift point
    exact (derivative state raw point shift).smul_const (ContinuousLinearMap.id ℂ (ComplexEuclidean 1))
  · exact rawEulerKernel_originalMoments kernels cost costBound
      (fun raw moment => Real.exp (parameters.sigma0+2*parameters.gamma)*constants raw moment)
      (fun raw moment => mul_nonneg (Real.exp_pos _).le (nonnegative raw moment)) momentBound

def originalSigmaComponentEulerFamily (parameters : PhaseParameters) (L compact : ℝ) (component : Fin 3) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialSigmaComponentKernel parameters L compact state.val radius component) :=
  scalarPrimitiveEulerFamily parameters L compact
    (fun state raw radius => sigmaScalar parameters L state.val.rho state.val.epsilon state.val.field state.val.low component raw radius)
    (fun state raw point shift => sigmaScalar_hasDerivAt parameters L state.val.rho state.val.epsilon state.val.field state.val.low component raw point shift)
    (fun state raw radius moment => radialSigmaCoefficients_moments parameters L compact state.val radius component raw moment)
    5 (by omega) (fun raw moment => sigmaScalarConstant parameters L component moment raw)
    (fun raw moment => sigmaScalarConstant_nonnegative parameters L component moment raw)
    (fun state raw radius moment => radialSigmaCoefficients_bound parameters L compact state.val radius component raw moment)

def originalRotatedSigmaComponentEulerFamily (parameters : PhaseParameters) (L compact : ℝ) (component : Fin 3) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialRotatedSigmaComponentKernel parameters L compact state.val radius component) :=
  scalarPrimitiveEulerFamily parameters L compact
    (fun state raw radius => angularCoefficientSequence (sigmaScalar parameters L state.val.rho state.val.epsilon state.val.field state.val.low component raw radius))
    (fun state raw point shift => (sigmaScalar_hasDerivAt parameters L state.val.rho state.val.epsilon state.val.field state.val.low component raw point shift).const_mul _)
    (fun state raw radius moment => (sigmaAngularScalarMoment_bound parameters L state.val.rho state.val.epsilon state.val.field state.val.low component moment raw radius.val radius.property.1 radius.property.2).1)
    6 (by omega) (fun raw moment => sigmaScalarConstant parameters L component (moment+1) raw)
    (fun raw moment => sigmaScalarConstant_nonnegative parameters L component (moment+1) raw)
    (fun state raw radius moment => (sigmaAngularScalarMoment_bound parameters L state.val.rho state.val.epsilon state.val.field state.val.low component moment raw radius.val radius.property.1 radius.property.2).2)

end Grad.OriginalCartesianTameEstimate
