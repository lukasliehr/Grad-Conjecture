import AIV6ExactHighDiagonalCommutation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalHigh
open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.AnnularHighTilt Grad.AnnularGrades

variable (lower length : ℝ) (positive : 0 < lower) (strict : lower < 1)
  (lengthPositive : 0 < length) (angular cell inserted : ℕ)

def originalNuDecode : originalNuGraph lower positive →L[ℂ] originalNuGraph lower positive :=
  originalNuDiagonal lower positive (fun mode => (annularGradeWeight angular cell inserted mode)⁻¹)
    1 (by norm_num) (annularGradeWeight_inv_bound angular cell inserted)

theorem originalNuDecode_pair (field : originalNuGraph lower positive) :
    originalNuPairEquivalence lower positive (originalNuDecode lower positive angular cell inserted field) =
      annularFluxGraphDecode lower positive angular cell inserted (originalNuPairEquivalence lower positive field) := by
  change (originalNuPairEquivalence lower positive)
    ((originalNuPairEquivalence lower positive).symm _) = _
  exact (originalNuPairEquivalence lower positive).apply_symm_apply _

/-- The original nu grade decoder has the exact literal weighted graph as range. -/
theorem originalNuGrade_iff (field : originalNuGraph lower positive) :
    HasAnnularFluxGrade lower positive angular cell inserted (originalNuPairEquivalence lower positive field) ↔
      ∃ weighted : originalNuGraph lower positive,
        originalNuDecode lower positive angular cell inserted weighted = field := by
  constructor
  · intro grade
    refine ⟨(originalNuPairEquivalence lower positive).symm
      (annularFluxGraphWeighted lower positive angular cell inserted
        (originalNuPairEquivalence lower positive field) grade), ?_⟩
    apply (originalNuPairEquivalence lower positive).injective
    rw [originalNuDecode_pair, (originalNuPairEquivalence lower positive).apply_symm_apply]
    exact annularFluxGraphDecode_weighted lower positive angular cell inserted _ grade
  · rintro ⟨weighted, rfl⟩
    rw [originalNuDecode_pair]
    exact annularFluxGraphDecode_hasGrade lower positive angular cell inserted _

theorem originalFluxTilt_decode (field : originalNuGraph lower positive) :
    originalFluxTiltEquivalence lower length positive strict.le lengthPositive
      (originalNuDecode lower positive angular cell inserted field) =
    annularOmegaGraphDecode lower length positive lengthPositive angular cell inserted
      (originalFluxTiltEquivalence lower length positive strict.le lengthPositive field) :=
  originalFluxTilt_diagonal lower length positive strict.le lengthPositive
    (fun mode => (annularGradeWeight angular cell inserted mode)⁻¹) 1 (by norm_num)
    (annularGradeWeight_inv_bound angular cell inserted) strict field

/-- The SAME equivalence preserves every original angular/cell/inserted grade. -/
theorem originalFluxTilt_grade_iff (field : originalNuGraph lower positive) :
    HasAnnularFluxGrade lower positive angular cell inserted (originalNuPairEquivalence lower positive field) ↔
    HasAnnularOmegaGrade lower angular cell inserted
      (originalFluxTiltEquivalence lower length positive strict.le lengthPositive field).val := by
  rw [originalNuGrade_iff, annularOmegaGraphGrade_iff]
  constructor
  · rintro ⟨weighted, rfl⟩
    exact ⟨originalFluxTiltEquivalence lower length positive strict.le lengthPositive weighted,
      (originalFluxTilt_decode lower length positive strict lengthPositive angular cell inserted weighted).symm⟩
  · rintro ⟨weighted, equality⟩
    refine ⟨(originalFluxTiltEquivalence lower length positive strict.le lengthPositive).symm weighted, ?_⟩
    apply (originalFluxTiltEquivalence lower length positive strict.le lengthPositive).injective
    rw [originalFluxTilt_decode lower length positive strict lengthPositive angular cell inserted, (originalFluxTiltEquivalence lower length positive strict.le lengthPositive).apply_symm_apply]
    exact equality

theorem originalEnergyTilt_decode (field : annularEnergySpace lower length positive) :
    highEnergyWeight lower length positive strict.le
      (annularEnergyDecode lower length positive angular cell inserted field) =
    annularEnergyDecode lower length positive angular cell inserted
      (highEnergyWeight lower length positive strict.le field) :=
  highEnergyWeight_diagonal lower length positive strict.le _ _ _ _ field

theorem originalEnergyTilt_grade_iff (field : annularEnergySpace lower length positive) :
    HasAnnularEnergyGrade lower length positive angular cell inserted field ↔
    HasAnnularEnergyGrade lower length positive angular cell inserted
      (highEnergyWeight lower length positive strict.le field) := by
  rw [← annularEnergyDecode_range_iff, ← annularEnergyDecode_range_iff]
  constructor
  · rintro ⟨weighted, rfl⟩
    exact ⟨highEnergyWeight lower length positive strict.le weighted,
      (originalEnergyTilt_decode lower length positive strict angular cell inserted weighted).symm⟩
  · rintro ⟨weighted, equality⟩
    refine ⟨highEnergyUnweight lower length positive strict.le weighted, ?_⟩
    apply (highEnergyTiltEquivalence lower length positive strict.le).injective
    change highEnergyWeight lower length positive strict.le
      (annularEnergyDecode lower length positive angular cell inserted
        (highEnergyUnweight lower length positive strict.le weighted)) = _
    rw [originalEnergyTilt_decode lower length positive strict angular cell inserted, highEnergy_weight_unweight]
    exact equality

end Grad.AnnularOriginalHigh
