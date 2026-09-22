import AKCV2OneHighInverseTaylorBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter Set
open scoped Topology ContDiff

namespace Grad.NashMoser.BranchDerivative

/-- NM11 for an actual zero branch on smooth cores. The derivative formula
is exactly -V DqPhi. The only remainder assumption is an estimate for the
inverse applied to the literal nonlinear Taylor remainder, which is supplied
by the one-high inverse/Taylor composition in the preceding module. -/
theorem exactZeroBranch_smooth_of_inverse_taylor
    {Parameter State Source Index : Type*}
    [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    [AddCommGroup State] [Module ℝ State] [AddCommGroup Source] [Module ℝ Source]
    (Grade : Index → Type*) [∀ index, NormedAddCommGroup (Grade index)]
    [∀ index, NormedSpace ℝ (Grade index)]
    (embedding : ∀ index, State →ₗ[ℝ] Grade index)
    (domain : Set Parameter) (openDomain : IsOpen domain) (low : Index)
    (mapping : Parameter → State → Source) (branch : Parameter → State)
    (continuous : ∀ index, ContinuousOn (fun point => embedding index (branch point)) domain)
    (zeros : ∀ point ∈ domain, mapping point (branch point) = 0)
    (parameterDerivative : Parameter → Parameter →ₗ[ℝ] Source)
    (stateDerivative : Parameter → State →ₗ[ℝ] Source)
    (inverse : Parameter → Source →ₗ[ℝ] State)
    (leftInverse : ∀ base ∈ domain, ∀ state, inverse base (stateDerivative base state) = state)
    (derivative : ∀ index, Parameter → Parameter →L[ℝ] Grade index)
    (derivativeFormula : ∀ index base, base ∈ domain → ∀ direction,
      derivative index base direction = -embedding index (inverse base (parameterDerivative base direction)))
    (inverseTaylor : ∀ base ∈ domain, ∀ index,
      ∃ (high : Index) (constant : ℝ), ∀ᶠ point in 𝓝 base,
        ‖embedding index (inverse base (coreTaylorRemainder mapping base point (branch base) (branch point)
          (parameterDerivative base) (stateDerivative base)))‖ ≤
          constant * (‖point-base‖+‖embedding high (branch point-branch base)‖) *
            (‖point-base‖+‖embedding low (branch point-branch base)‖))
    (realizations : ∀ (order : ℕ) (index : Index),
      ∃ (input : Index) (neighborhood : Set (Parameter × Grade input))
        (realization : Parameter × Grade input → Parameter →L[ℝ] Grade index),
        MapsTo (fun point => (point, embedding input (branch point))) domain neighborhood ∧
        ContDiffOn ℝ order realization neighborhood ∧
        ∀ point ∈ domain, derivative index point = realization (point, embedding input (branch point))) :
    (∀ index base, base ∈ domain →
      HasFDerivAt (fun point => embedding index (branch point)) (derivative index base) base) ∧
    ∀ index, ContDiffOn ℝ ∞ (fun point => embedding index (branch point)) domain := by
  apply allGrade_contDiffOn_of_inverse_remainder Grade domain openDomain low
    (fun index point => embedding index (branch point)) continuous derivative ?_ realizations
  intro base member index
  obtain ⟨high, constant, bound⟩ := inverseTaylor base member index
  refine ⟨high, constant, ?_⟩
  filter_upwards [bound, openDomain.mem_nhds member] with point bound pointMember
  have same := congrArg (fun state => ‖embedding index state‖)
    (inverse_two_zero_difference mapping base point (branch base) (branch point)
      (parameterDerivative base) (stateDerivative base) (inverse base) (leftInverse base member)
      (zeros base member) (zeros point pointMember))
  have remainderNorm :
      ‖embedding index (branch point)-embedding index (branch base)-derivative index base (point-base)‖ =
      ‖embedding index (inverse base (coreTaylorRemainder mapping base point (branch base) (branch point)
        (parameterDerivative base) (stateDerivative base)))‖ := by
    rw [derivativeFormula index base member]
    simpa only [map_sub, map_neg, LinearMap.neg_apply, LinearMap.comp_apply, norm_neg,
      neg_sub, neg_sub_neg] using same
  rw [remainderNorm]
  simpa only [map_sub] using bound

end Grad.NashMoser.BranchDerivative
