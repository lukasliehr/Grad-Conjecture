import AKDD7SamePrimitiveEulerOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.Allocation

/-- The written SR13 physical allocation on the SAME reconstruction-state
carrier. Constants precede every state and radius, at original width. -/
def OriginalEulerMoments (parameters : PhaseParameters) (L compact : ℝ) {source target : ℕ}
    (kernels : (state : AnnularReconstructionState parameters L compact) → ℕ →
      (radius : RadialPoint) → RadialKernel parameters radius source target) : Prop :=
  ∀ rank moment, ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ state, physicalBudget parameters state.val.field state.val.rho state.val.epsilon 10 ≤ 1 → ∀ radius,
      fullKernelMoment (radialKernelParameters parameters radius) moment (kernels state rank radius) ≤
        constant*(1+physicalBudget parameters state.val.field state.val.rho state.val.epsilon (10+(rank+moment)))

theorem OriginalEulerMoments.fixed {source target : ℕ} (parameters : PhaseParameters) (L compact : ℝ)
    (family : (phase : PhaseParameters) → FullTwoFrequencyKernel phase source target)
    (same : ∀ first second, SameKernelEntries (family first) (family second)) :
    OriginalEulerMoments parameters L compact (fun _ => fixedEulerKernel parameters family) := by
  intro rank moment
  let constant := fullKernelMoment (maximalKernelParameters parameters) moment (family (maximalKernelParameters parameters))
  refine ⟨constant,fullKernelMoment_nonnegative _ _ _,?_⟩
  intro state _ radius
  apply (fixedEulerKernel_moment parameters family same rank moment radius).trans
  exact le_mul_of_one_le_right (fullKernelMoment_nonnegative _ _ _)
    (by linarith [physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon (10+(rank+moment))])

theorem OriginalEulerMoments.add {parameters : PhaseParameters} {L compact : ℝ} {source target : ℕ}
    {first second : (state : AnnularReconstructionState parameters L compact) → ℕ →
      (radius : RadialPoint) → RadialKernel parameters radius source target}
    (one : OriginalEulerMoments parameters L compact first) (two : OriginalEulerMoments parameters L compact second) :
    OriginalEulerMoments parameters L compact (fun state rank radius => fullKernelAdd (first state rank radius) (second state rank radius)) := by
  intro rank moment
  obtain ⟨firstConstant,first0,firstBound⟩ := one rank moment
  obtain ⟨secondConstant,second0,secondBound⟩ := two rank moment
  refine ⟨firstConstant+secondConstant,add_nonneg first0 second0,?_⟩
  intro state low radius
  exact (fullKernelAdd_moment_le _ moment _ _).trans
    ((add_le_add (firstBound state low radius) (secondBound state low radius)).trans_eq (by ring))

theorem OriginalEulerMoments.neg {parameters : PhaseParameters} {L compact : ℝ} {source target : ℕ}
    {kernels : (state : AnnularReconstructionState parameters L compact) → ℕ →
      (radius : RadialPoint) → RadialKernel parameters radius source target}
    (bounded : OriginalEulerMoments parameters L compact kernels) :
    OriginalEulerMoments parameters L compact (fun state rank radius => fullKernelNeg (kernels state rank radius)) := by
  intro rank moment
  obtain ⟨constant,nonnegative,bound⟩ := bounded rank moment
  exact ⟨constant,nonnegative,fun state low radius => (fullKernelNeg_moment_le _ moment _).trans (bound state low radius)⟩

theorem OriginalEulerMoments.comp {parameters : PhaseParameters} {L compact : ℝ} {source middle target : ℕ}
    {outer : (state : AnnularReconstructionState parameters L compact) → ℕ →
      (radius : RadialPoint) → RadialKernel parameters radius middle target}
    {inner : (state : AnnularReconstructionState parameters L compact) → ℕ →
      (radius : RadialPoint) → RadialKernel parameters radius source middle}
    (one : OriginalEulerMoments parameters L compact outer) (two : OriginalEulerMoments parameters L compact inner) :
    OriginalEulerMoments parameters L compact (fun state rank radius => compositionEulerKernel radius
      (fun raw => outer state raw radius) (fun raw => inner state raw radius) (eulerLeibnizTerms rank)) := by
  choose outerConstants outer0 outerBound using one
  choose innerConstants inner0 innerBound using two
  intro rank moment
  refine ⟨compositionEulerMomentConstant 10 outerConstants innerConstants rank moment,
    compositionEulerMomentConstant_nonnegative 10 outerConstants innerConstants outer0 inner0 rank moment,?_⟩
  intro state low radius
  exact compositionEulerKernel_oneHigh parameters state.val.field state.val.rho state.val.epsilon radius 10 low
    (fun raw => outer state raw radius) (fun raw => inner state raw radius) outerConstants innerConstants outer0 inner0
    (fun raw moment => outerBound raw moment state low radius) (fun raw moment => innerBound raw moment state low radius) rank moment

/-- Inverse closure uses the accepted SAME base inverse moment estimate,
and differentiates only the exact ordered factors before interpolation. -/
theorem OriginalEulerMoments.negativeInverse {parameters : PhaseParameters} {L compact : ℝ} {dimension : ℕ}
    {kernels : (state : AnnularReconstructionState parameters L compact) → ℕ →
      (radius : RadialPoint) → RadialKernel parameters radius dimension dimension}
    (bounded : OriginalEulerMoments parameters L compact kernels)
    (low : ℝ) (small : low < 1)
    (lowBound : ∀ state radius, fullKernelMoment (radialKernelParameters parameters radius) 0 (kernels state 0 radius) ≤ low)
    (baseMoments : RadialPhysicalMoments parameters L compact (fun state radius =>
      fullKernelNegativeIdentityInverse (radialKernelParameters parameters radius) (kernels state 0 radius) low (lowBound state radius) small)) :
    OriginalEulerMoments parameters L compact (fun state rank radius =>
      sameNegativeInverseEulerKernel parameters radius (fun raw => kernels state raw radius) low small (lowBound state radius) rank) := by
  choose forwardConstants forward0 forwardBound using bounded
  choose inverseConstants inverse0 inverseBound using baseMoments
  intro rank moment
  refine ⟨inverseExpressionMomentConstant 10 inverseConstants forwardConstants (inverseEulerExpression rank) moment,
    inverseExpressionMomentConstant_nonnegative 10 inverseConstants forwardConstants inverse0 forward0 _ _,?_⟩
  intro state physicalLow radius
  apply inverseEulerWords_oneHigh parameters state.val.field state.val.rho state.val.epsilon radius 10 physicalLow
    (fullKernelNegativeIdentityInverse (radialKernelParameters parameters radius) (kernels state 0 radius) low (lowBound state radius) small)
    (fun raw => kernels state raw radius) inverseConstants forwardConstants inverse0 forward0
  · intro moment
    have bound := inverseBound moment state radius
    apply bound.trans
    apply mul_le_mul_of_nonneg_left _ (inverse0 moment)
    change 1+physicalBudget parameters state.val.field state.val.rho state.val.epsilon (moment+7) ≤
      1+physicalBudget parameters state.val.field state.val.rho state.val.epsilon (10+moment)
    exact add_le_add le_rfl (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by omega))
  · intro raw moment
    exact forwardBound raw moment state physicalLow radius

end Grad.OriginalCartesianTameEstimate
