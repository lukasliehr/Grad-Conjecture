import AKDE13ConstructedTiltRemainder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff Topology
namespace Grad.OriginalCellFamily

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- One compact parameter mean-value bound for the actual smooth packet.
The packet may contain spatial derivatives; its zero value is literal. -/
theorem compactParameter_zero_bound (radius : ℝ) (positive : 0 < radius)
    (domain : Set E) (openDomain : IsOpen domain) (compact : Set E) (compactSet : IsCompact compact)
    (included : compact ⊆ domain) (field : ℝ × E → G)
    (smooth : ContDiffOn ℝ ∞ field (Ioo (-radius) radius ×ˢ domain))
    (zero : ∀ point ∈ compact, field (0,point)=0) :
    ∃ constant : ℝ, 1 ≤ constant ∧ ∀ epsilon : ℝ, |epsilon| ≤ radius/2 →
      ∀ point ∈ compact, ‖field (epsilon,point)‖ ≤ constant * |epsilon| := by
  have compactIncluded : Icc (-radius/2) (radius/2) ×ˢ compact ⊆ Ioo (-radius) radius ×ˢ domain := by
    intro point member
    exact ⟨⟨by linarith [member.1.1],by linarith [member.1.2]⟩,included member.2⟩
  have derivativeContinuous := (smooth.fderiv_of_isOpen (m := ∞) (isOpen_Ioo.prod openDomain) (by simp)).continuousOn
  obtain ⟨rawBound,bounded⟩ := (isCompact_Icc.prod compactSet).bddAbove_image
    ((derivativeContinuous.mono compactIncluded).norm)
  refine ⟨max 1 rawBound,le_max_left _ _,?_⟩
  intro epsilon epsilonSmall point pointIn
  have insertionDerivative (value : ℝ) : HasDerivAt (fun value : ℝ => (value,point)) (1,0) value :=
    (hasDerivAt_id value).prodMk (hasDerivAt_const value point)
  have differentiable (value : ℝ) (valueIn : value ∈ Icc (-radius/2) (radius/2)) :
      DifferentiableAt ℝ field (value,point) :=
    (smooth.contDiffAt ((isOpen_Ioo.prod openDomain).mem_nhds
      (compactIncluded ⟨valueIn,pointIn⟩))).differentiableAt (by simp)
  have sectionDifferentiable (value : ℝ) (valueIn : value ∈ Icc (-radius/2) (radius/2)) :
      DifferentiableAt ℝ (fun value => field (value,point)) value :=
    (differentiable value valueIn).comp value (insertionDerivative value).differentiableAt
  have sectionBound (value : ℝ) (valueIn : value ∈ Icc (-radius/2) (radius/2)) :
      ‖deriv (fun value => field (value,point)) value‖ ≤ max 1 rawBound := by
    have law := ((differentiable value valueIn).hasFDerivAt.comp_hasDerivAt value (insertionDerivative value)).deriv
    change deriv (fun value => field (value,point)) value = _ at law
    rw [law]
    calc
      _ ≤ ‖fderiv ℝ field (value,point)‖ * ‖((1,0) : ℝ × E)‖ := (fderiv ℝ field (value,point)).le_opNorm _
      _ = ‖fderiv ℝ field (value,point)‖ := by simp
      _ ≤ rawBound := bounded ⟨(value,point),⟨valueIn,pointIn⟩,rfl⟩
      _ ≤ max 1 rawBound := le_max_right _ _
  have estimate := Convex.norm_image_sub_le_of_norm_deriv_le sectionDifferentiable sectionBound
    (convex_Icc _ _) (show (0:ℝ)∈Icc (-radius/2) (radius/2) from ⟨by linarith,by linarith⟩)
    (show epsilon∈Icc (-radius/2) (radius/2) from ⟨by linarith [(abs_le.mp epsilonSmall).1],(abs_le.mp epsilonSmall).2⟩)
  simpa only [zero point pointIn,sub_zero,Real.norm_eq_abs] using estimate

end Grad.OriginalCellFamily
