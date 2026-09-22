import QS5Consumer
import QR7CompletedQuotientReality

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.RealFixedRanges

section Retraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Project, then average with the real involution. -/
def realAverage (projection symmetry : E →L[ℝ] E) : E →L[ℝ] E :=
  (1 / 2 : ℝ) • (projection + symmetry.comp projection)

theorem realAverage_mem (projection symmetry : E →L[ℝ] E)
    (idem : ∀ x, projection (projection x) = projection x)
    (involutive : Function.Involutive symmetry)
    (commutes : ∀ x, projection (symmetry x) = symmetry (projection x)) (x : E) :
    realAverage projection symmetry x ∈ jointFixed projection symmetry := by
  rw [mem_jointFixed]
  change projection ((1 / 2 : ℝ) • (projection x + symmetry (projection x))) = _ ∧
    symmetry ((1 / 2 : ℝ) • (projection x + symmetry (projection x))) = _
  constructor
  · simp only [map_smul, map_add, commutes, idem]
    rfl
  · simp only [map_smul, map_add]
    rw [involutive (projection x)]
    change (1 / 2 : ℝ) • (symmetry (projection x) + projection x) =
      (1 / 2 : ℝ) • (projection x + symmetry (projection x))
    rw [add_comm]

def realRetraction (projection symmetry : E →L[ℝ] E)
    (idem : ∀ x, projection (projection x) = projection x)
    (involutive : Function.Involutive symmetry)
    (commutes : ∀ x, projection (symmetry x) = symmetry (projection x)) :
    E →L[ℝ] jointFixed projection symmetry :=
  (realAverage projection symmetry).codRestrict (jointFixed projection symmetry)
    (realAverage_mem projection symmetry idem involutive commutes)

theorem realRetraction_fixes (projection symmetry : E →L[ℝ] E)
    (idem : ∀ x, projection (projection x) = projection x)
    (involutive : Function.Involutive symmetry)
    (commutes : ∀ x, projection (symmetry x) = symmetry (projection x))
    (x : jointFixed projection symmetry) :
    realRetraction projection symmetry idem involutive commutes x = x := by
  apply Subtype.ext
  have fixed := (mem_jointFixed projection symmetry x.val).1 x.property
  change (1 / 2 : ℝ) • (projection x.val + symmetry (projection x.val)) = x.val
  rw [fixed.1, fixed.2]
  module

theorem realRetraction_surjective (projection symmetry : E →L[ℝ] E)
    (idem : ∀ x, projection (projection x) = projection x)
    (involutive : Function.Involutive symmetry)
    (commutes : ∀ x, projection (symmetry x) = symmetry (projection x)) :
    Function.Surjective (realRetraction projection symmetry idem involutive commutes) :=
  fun x => ⟨x.val, realRetraction_fixes projection symmetry idem involutive commutes x⟩

end Retraction

open Grad.CartesianState Grad.AxisCore Grad.QuotientProjection Grad.CompletedReality

def sourceRetraction (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    ZAmbient parameters grade →L[ℝ] sourceRange parameters grade large :=
  realRetraction ((sourceProjection parameters grade large).restrictScalars ℝ)
    (zConjugation parameters grade).toContinuousLinearEquiv.toContinuousLinearMap
    (sourceProjection_idempotent parameters grade large)
    (zConjugation_involutive parameters grade)
    (fun x => (completedQuotientProjection_conjugate parameters grade
      (sourceProjection parameters grade large) (sourceProjection_core parameters grade large) x).symm)

theorem sourceRetraction_surjective (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    Function.Surjective (sourceRetraction parameters grade large) :=
  realRetraction_surjective _ _ _ _ _

end Grad.RealFixedRanges
