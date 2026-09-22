import QT1RealRetraction

noncomputable section

namespace Grad.RealFixedRanges

open Grad.CartesianState Grad.AxisCore Grad.QuotientProjection Grad.CompletedReality

def sourceRealApproximation (parameters : PhaseParameters) (field : SmoothQuotient parameters) :
    SmoothQuotient parameters :=
  (1 / 2 : ℝ) • (quotientProjection parameters field +
    zCoreConjugation parameters (quotientProjection parameters field))

theorem sourceRetraction_eta (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade)
    (field : SmoothQuotient parameters) :
    (sourceRetraction parameters grade large (quotientEta parameters grade field)).val =
      quotientEta parameters grade (sourceRealApproximation parameters field) := by
  change (1 / 2 : ℝ) • (sourceProjection parameters grade large (quotientEta parameters grade field) +
    zConjugation parameters grade (sourceProjection parameters grade large (quotientEta parameters grade field))) = _
  rw [sourceProjection_core, zConjugation_quotientEta]
  change _ = ((quotientEta parameters grade).restrictScalars ℝ)
    ((1 / 2 : ℝ) • (quotientProjection parameters field +
      zCoreConjugation parameters (quotientProjection parameters field)))
  rw [map_smul, map_add]
  rfl

theorem sourceRealApproximation_mem (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade)
    (field : SmoothQuotient parameters) :
    sourceRealApproximation parameters field ∈ sourceSmoothRange parameters := by
  apply (quotientEta_mem_iff parameters grade large _).1
  rw [← sourceRetraction_eta]
  exact (sourceRetraction parameters grade large (quotientEta parameters grade field)).property

/-- COR24's actual quotient-side projected-real density. State density and
the two completion-equivalence clauses remain separate obligations. -/
theorem sourceSmoothEmbedding_denseRange (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    DenseRange (sourceSmoothEmbedding parameters grade large) := by
  have dense := (sourceRetraction_surjective parameters grade large).denseRange.comp
    (quotientEta_denseRange parameters grade) (sourceRetraction parameters grade large).continuous
  apply dense.mono
  rintro _ ⟨field, rfl⟩
  refine ⟨⟨sourceRealApproximation parameters field,
    sourceRealApproximation_mem parameters grade large field⟩, ?_⟩
  apply Subtype.ext
  exact (sourceRetraction_eta parameters grade large field).symm

end Grad.RealFixedRanges
