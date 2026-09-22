import AKCV7OriginalTaylorRemainderRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff
namespace Grad.NashMoser.BranchDerivative

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Taylor's second-order remainder on one segment, with a bound on the
actual second derivative applied twice to its displacement. The input and
output need only be normed spaces; no norm is assigned to the smooth core. -/
theorem segment_taylor_remainder_bound
    (mapping : E → F) (domain : Set E) (openDomain : IsOpen domain)
    (smooth : ContDiffOn ℝ ∞ mapping domain) (base direction : E)
    (segmentInside : ∀ t ∈ Icc (0 : ℝ) 1, base + t • direction ∈ domain)
    (bound : ℝ)
    (secondBound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ 2 mapping (base+t•direction) (fun _ => direction)‖ ≤ bound) :
    ‖mapping (base+direction)-mapping base-fderiv ℝ mapping base direction‖ ≤ bound := by
  let path : ℝ → E := fun t => base+t•direction
  let value : ℝ → F := fun t => mapping (path t)
  let first : ℝ → F := fun t => fderiv ℝ mapping (path t) direction
  have pathDerivative (t : ℝ) : HasDerivAt path direction t := by
    simpa only [path,id_eq,one_smul] using ((hasDerivAt_id t).smul_const direction).const_add base
  have firstSmooth : ContDiffOn ℝ ∞ (fderiv ℝ mapping) domain :=
    smooth.fderiv_of_isOpen openDomain (by simp)
  have valueDerivative (t : ℝ) (inside : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt value (first t) t :=
    ((smooth.contDiffAt (openDomain.mem_nhds (segmentInside t inside))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t (pathDerivative t)
  have firstDerivative (t : ℝ) (inside : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt first (fderiv ℝ (fderiv ℝ mapping) (path t) direction direction) t := by
    have outer := ((firstSmooth.contDiffAt (openDomain.mem_nhds (segmentInside t inside))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t (pathDerivative t)
    simpa only [first,path,Function.comp_apply,map_zero,add_zero] using outer.clm_apply (hasDerivAt_const t direction)
  have secondNorm (t : ℝ) (inside : t ∈ Icc (0 : ℝ) 1) :
      ‖fderiv ℝ (fderiv ℝ mapping) (path t) direction direction‖ ≤ bound := by
    simpa only [iteratedFDeriv_two_apply] using secondBound t inside
  have boundNonnegative : 0 ≤ bound := (norm_nonneg _).trans
    (secondNorm 0 (by constructor <;> norm_num))
  have firstDifference (t : ℝ) (inside : t ∈ Icc (0 : ℝ) 1) :
      ‖first t-first 0‖ ≤ bound := by
    have estimate := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun u hu => (firstDerivative u hu).hasDerivWithinAt)
      (fun u hu => secondNorm u ⟨hu.1,hu.2.le⟩) t inside
    rw [sub_zero] at estimate
    exact estimate.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left inside.2 boundNonnegative)
  let remainder : ℝ → F := fun t => value t-t•first 0
  have remainderDerivative (t : ℝ) (inside : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt remainder (first t-first 0) t := by
    exact ((valueDerivative t inside).sub
      ((hasDerivAt_id t).smul_const (first 0))).congr_deriv (by simp only [one_smul])
  have estimate := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (remainderDerivative t ht).hasDerivWithinAt)
    (fun t ht => firstDifference t ⟨ht.1,ht.2.le⟩)
    1 (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  have rearrange : remainder 1-remainder 0 =
      mapping (base+direction)-mapping base-fderiv ℝ mapping base direction := by
    simp only [remainder,value,first,path,one_smul,zero_smul,add_zero,sub_zero]
    abel
  simpa only [rearrange,sub_zero,mul_one] using estimate

end Grad.NashMoser.BranchDerivative
