import AKCT2FiniteInputSmoothBranchBootstrap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter Set
open scoped Topology ContDiff

namespace Grad.NashMoser.BranchDerivative

private theorem two_scale_factor_tendsto_zero
    {Parameter High : Type*} [NormedAddCommGroup Parameter] [NormedAddCommGroup High]
    (branch : Parameter → High) (base : Parameter) (constant : ℝ)
    (continuous : ContinuousAt branch base) :
    Tendsto (fun point => constant * (‖point-base‖+‖branch point-branch base‖))
      (𝓝 base) (𝓝 0) := by
  have factorContinuous : ContinuousAt
      (fun point => constant * (‖point-base‖+‖branch point-branch base‖)) base :=
    continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).norm.add
      (continuous.sub continuousAt_const).norm)
  simpa only [sub_self, norm_zero, add_zero, mul_zero] using factorContinuous.tendsto

/-- The NM11 inverse-Taylor estimate and all-grade continuity imply the
actual derivative in every grade. The controlling high grade may depend on
the base point and output grade; the absorbed low grade stays fixed. -/
theorem allGrade_hasFDerivAt_of_inverse_remainder
    {Parameter Index : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    (Grade : Index → Type*) [∀ index, NormedAddCommGroup (Grade index)]
    [∀ index, NormedSpace ℝ (Grade index)]
    (domain : Set Parameter) (openDomain : IsOpen domain) (low : Index)
    (branch : ∀ index, Parameter → Grade index)
    (continuous : ∀ index, ContinuousOn (branch index) domain)
    (derivative : ∀ index, Parameter → Parameter →L[ℝ] Grade index)
    (inverseRemainder : ∀ base ∈ domain, ∀ index,
      ∃ (high : Index) (constant : ℝ), ∀ᶠ point in 𝓝 base,
        ‖branch index point-branch index base-derivative index base (point-base)‖ ≤
          constant * (‖point-base‖+‖branch high point-branch high base‖) *
            (‖point-base‖+‖branch low point-branch low base‖)) :
    ∀ index base, base ∈ domain → HasFDerivAt (branch index) (derivative index base) base := by
  intro index base member
  obtain ⟨lowHigh, lowConstant, lowRemainder⟩ := inverseRemainder base member low
  obtain ⟨high, constant, remainder⟩ := inverseRemainder base member index
  have lowContinuous := (continuous lowHigh base member).continuousAt (openDomain.mem_nhds member)
  have highContinuous := (continuous high base member).continuousAt (openDomain.mem_nhds member)
  exact branch_hasFDerivAt_of_two_scale_remainder (branch low) (branch index) base
    (derivative low base) (derivative index base)
    (fun point => lowConstant * (‖point-base‖+‖branch lowHigh point-branch lowHigh base‖))
    (fun point => constant * (‖point-base‖+‖branch high point-branch high base‖))
    (two_scale_factor_tendsto_zero (branch lowHigh) base lowConstant lowContinuous)
    (two_scale_factor_tendsto_zero (branch high) base constant highContinuous)
    lowRemainder remainder

/-- Full written NM11 analytic implication: the inverse remainder proves
the derivative first, then finite-input smooth derivative realizations give
all finite parameter orders for the SAME continuous branch. -/
theorem allGrade_contDiffOn_of_inverse_remainder
    {Parameter Index : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    (Grade : Index → Type*) [∀ index, NormedAddCommGroup (Grade index)]
    [∀ index, NormedSpace ℝ (Grade index)]
    (domain : Set Parameter) (openDomain : IsOpen domain) (low : Index)
    (branch : ∀ index, Parameter → Grade index)
    (continuous : ∀ index, ContinuousOn (branch index) domain)
    (derivative : ∀ index, Parameter → Parameter →L[ℝ] Grade index)
    (inverseRemainder : ∀ base ∈ domain, ∀ index,
      ∃ (high : Index) (constant : ℝ), ∀ᶠ point in 𝓝 base,
        ‖branch index point-branch index base-derivative index base (point-base)‖ ≤
          constant * (‖point-base‖+‖branch high point-branch high base‖) *
            (‖point-base‖+‖branch low point-branch low base‖))
    (realizations : ∀ (order : ℕ) (index : Index),
      ∃ (input : Index) (neighborhood : Set (Parameter × Grade input))
        (realization : Parameter × Grade input → Parameter →L[ℝ] Grade index),
        MapsTo (fun point => (point, branch input point)) domain neighborhood ∧
        ContDiffOn ℝ order realization neighborhood ∧
        ∀ point ∈ domain, derivative index point = realization (point, branch input point)) :
    (∀ index base, base ∈ domain → HasFDerivAt (branch index) (derivative index base) base) ∧
      ∀ index, ContDiffOn ℝ ∞ (branch index) domain := by
  have hasDerivative := allGrade_hasFDerivAt_of_inverse_remainder Grade domain openDomain low
    branch continuous derivative inverseRemainder
  exact ⟨hasDerivative, allGrade_contDiffOn_of_finite_input_derivative Grade domain openDomain
    branch derivative hasDerivative realizations⟩

end Grad.NashMoser.BranchDerivative
