import QY1ActualRange

noncomputable section

open scoped ContDiff

namespace Grad.Q24Realization

section ExactRestriction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Restrict only the codomain of the proved literal map on its domain.
The value outside the domain is irrelevant and set to zero, not projected. -/
def exactRangeRestriction (mapping : E → F) (domain : Set E) (target : Submodule ℝ F)
    (range : Set.MapsTo mapping domain target) : E → target := by
  classical
  exact fun point => if inside : point ∈ domain then ⟨mapping point, range inside⟩ else 0

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem exactRangeRestriction_coe (mapping : E → F) (domain : Set E) (target : Submodule ℝ F)
    (range : Set.MapsTo mapping domain target) (point : E) (inside : point ∈ domain) :
    (exactRangeRestriction mapping domain target range point).val = mapping point := by
  simp only [exactRangeRestriction, dif_pos inside]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem exactRangeRestriction_eq_retraction (mapping : E → F) (domain : Set E)
    (target : Submodule ℝ F) (range : Set.MapsTo mapping domain target)
    (retraction : F →L[ℝ] target) (fixes : ∀ value : target, retraction value = value)
    (point : E) (inside : point ∈ domain) :
    exactRangeRestriction mapping domain target range point = retraction (mapping point) := by
  simpa only [exactRangeRestriction, dif_pos inside] using (fixes ⟨mapping point, range inside⟩).symm

theorem exactRangeRestriction_contDiffOn (mapping : E → F) (domain : Set E)
    (target : Submodule ℝ F) (range : Set.MapsTo mapping domain target)
    (retraction : F →L[ℝ] target) (fixes : ∀ value : target, retraction value = value)
    (smooth : ContDiffOn ℝ ∞ mapping domain) :
    ContDiffOn ℝ ∞ (exactRangeRestriction mapping domain target range) domain := by
  apply (smooth.continuousLinearMap_comp retraction).congr
  intro point inside
  exact exactRangeRestriction_eq_retraction mapping domain target range retraction fixes point inside

/-- The genuine iterated derivative of the exact codomain restriction
includes as the genuine ambient derivative on the original open domain. -/
theorem exactRangeRestriction_derivative_coe (mapping : E → F) (domain : Set E)
    (target : Submodule ℝ F) (range : Set.MapsTo mapping domain target)
    (retraction : F →L[ℝ] target) (fixes : ∀ value : target, retraction value = value)
    (openDomain : IsOpen domain) (smooth : ContDiffOn ℝ ∞ mapping domain)
    (order : ℕ) (point : E) (inside : point ∈ domain) (directions : Fin order → E) :
    (iteratedFDeriv ℝ order (exactRangeRestriction mapping domain target range) point directions).val =
      iteratedFDeriv ℝ order mapping point directions := by
  have restrictedSmooth := exactRangeRestriction_contDiffOn mapping domain target range retraction fixes smooth
  have composed := target.subtypeL.iteratedFDeriv_comp_left
    ((restrictedSmooth point inside).contDiffAt (openDomain.mem_nhds inside))
    (show (order : WithTop ℕ∞) ≤ ∞ by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  have same : Set.EqOn (target.subtypeL ∘ exactRangeRestriction mapping domain target range) mapping domain :=
    fun value member => exactRangeRestriction_coe mapping domain target range value member
  have derivatives := iteratedFDerivWithin_congr (𝕜 := ℝ) same inside order
  rw [iteratedFDerivWithin_of_isOpen order openDomain inside,
    iteratedFDerivWithin_of_isOpen order openDomain inside] at derivatives
  rw [derivatives] at composed
  exact (congrArg (fun derivative => derivative directions) composed).symm

end ExactRestriction

end Grad.Q24Realization
