import AKDD20ActualNormalizedRowsOriginalPhase

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularRadialSmoothness Grad.AnnularKernelContinuity
open Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation

/-- Internal row assembly for the actual physical polar cofactor and
retained force rows. The scalar primitive constants precede every state. -/
def rowPrimitiveEulerFamily (parameters : PhaseParameters) (L compact : ℝ)
    (coefficients : AnnularReconstructionState parameters L compact → ℕ → ℝ → Fin 3 → (ℤ × ℤ) → ℂ)
    (derivative : ∀ state raw point component shift, HasDerivAt (fun radius => coefficients state raw radius component shift)
      (coefficients state (raw+1) point component shift) point)
    (summable : ∀ state raw (radius : RadialPoint) component moment,
      Summable (productMoment parameters moment radius.val (coefficients state raw radius.val component)))
    (cost : ℕ) (costBound : cost ≤ 10) (constants : Fin 3 → ℕ → ℕ → ℝ)
    (nonnegative : ∀ component raw moment, 0 ≤ constants component raw moment)
    (bounds : ∀ state raw (radius : RadialPoint) component moment,
      (∑' shift, productMoment parameters moment radius.val (coefficients state raw radius.val component) shift) ≤
        constants component raw moment * physicalBudget parameters state.val.field state.val.rho state.val.epsilon (moment+raw+cost)) :
    ActualEulerFamily parameters L compact (fun state radius =>
      radialRowKernel parameters radius 3 (coefficients state 0 radius.val) (summable state 0 radius)) := by
  let kernels := fun (state : AnnularReconstructionState parameters L compact) (raw : ℕ) (radius : RadialPoint) =>
    radialRowKernel parameters radius 3 (coefficients state raw radius.val) (summable state raw radius)
  have momentBound (state : AnnularReconstructionState parameters L compact) (raw moment : ℕ) (radius : RadialPoint) :
      fullKernelMoment (radialKernelParameters parameters radius) moment (kernels state raw radius) ≤
        (Real.exp (parameters.sigma0+2*parameters.gamma)*(∑ component,constants component raw moment)) *
          physicalBudget parameters state.val.field state.val.rho state.val.epsilon (moment+raw+cost) := by
    apply (radialRowKernel_moment_le parameters radius 3 moment _ _).trans
    have summed := Finset.sum_le_sum (s := Finset.univ) (fun component _ => bounds state raw radius component moment)
    apply (mul_le_mul_of_nonneg_left summed (Real.exp_pos _).le).trans_eq
    rw [← Finset.sum_mul]
    ring
  have regular (state : AnnularReconstructionState parameters L compact) (raw : ℕ) :
      RegularKernelFamily (kernels state raw) := by
    refine regularKernelFamily_of_bound _ ?_ _ (fun moment radius => momentBound state raw moment radius)
    intro shift input
    refine rowMultiplicationEntry_continuous 3 (fun radius : RadialPoint => coefficients state raw radius.val) ?_ shift input
    intro component shift
    have continuousCoefficient : Continuous (fun point => coefficients state raw point component shift) :=
      continuous_iff_continuousAt.mpr (fun point => (derivative state raw point component shift).continuousAt)
    exact continuousCoefficient.comp continuous_subtype_val
  refine ⟨(fun state rank radius => actualRawEulerKernel radius (fun raw => kernels state raw radius) rank),
    (fun _ _ => rfl),?_,?_⟩
  · intro state lower positive bounded
    apply actualRawEulerKernel_derivativeTower
    intro raw radius inside
    apply actualMatrixKernelAction_hasDerivWithinAt parameters lower positive bounded (kernels state)
      (fun raw point shift => rowMultiplicationEntry 3 (coefficients state raw point) shift (0,0))
      (fun _ _ _ _ => rfl) _ (regular state) raw radius inside
    intro raw shift point
    exact rowMultiplicationEntry_hasDerivAt 3 _ _
      (fun component point shift => derivative state raw point component shift) point shift (0,0)
  · exact rawEulerKernel_originalMoments kernels cost costBound
      (fun raw moment => Real.exp (parameters.sigma0+2*parameters.gamma)*(∑ component,constants component raw moment))
      (fun raw moment => mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg (fun component _ => nonnegative component raw moment))) momentBound

end Grad.OriginalCartesianTameEstimate
