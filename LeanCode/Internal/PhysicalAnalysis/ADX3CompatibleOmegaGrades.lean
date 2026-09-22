import ADX2LiteralOmegaGrades

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularOmegaGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularGrades Grad.AnnularFluxTrace
open Grad.CircularHighRegularity Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.WeightedTrace

section Inclusion
variable (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (angular cell inserted largerAngular largerCell largerInserted : ℕ)
    (angularLe : angular ≤ largerAngular) (cellLe : cell ≤ largerCell)
    (insertedLe : inserted ≤ largerInserted)

/-- Natural inclusion between arbitrary split/inserted Domega grades.
The same ratio multiplies both literal coordinates. -/
def annularOmegaGradeInclusion :
    annularOmegaGraph lower length positive lengthPositive →L[ℂ]
      annularOmegaGraph lower length positive lengthPositive :=
  annularOmegaGraphDiagonal lower length positive lengthPositive
    (fun mode => annularGradeWeight angular cell inserted mode /
      annularGradeWeight largerAngular largerCell largerInserted mode)
    1 (by norm_num)
    (annularGradeWeight_ratio_bound angular cell inserted largerAngular largerCell largerInserted
      angularLe cellLe insertedLe)

/-- Decoding after grade inclusion gives exactly the same physical Domega
field as decoding at the larger grade, on both coordinates. -/
theorem annularOmegaGradeInclusion_decode
    (field : annularOmegaGraph lower length positive lengthPositive) :
    annularOmegaGraphDecode lower length positive lengthPositive angular cell inserted
      (annularOmegaGradeInclusion lower length positive lengthPositive angular cell inserted
        largerAngular largerCell largerInserted angularLe cellLe insertedLe field) =
    annularOmegaGraphDecode lower length positive lengthPositive largerAngular largerCell largerInserted field := by
  apply Subtype.ext
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · have result :
        (annularOmegaGraphDecode lower length positive lengthPositive angular cell inserted
          (annularOmegaGradeInclusion lower length positive lengthPositive angular cell inserted
            largerAngular largerCell largerInserted angularLe cellLe insertedLe field)).val 0 =
        (annularOmegaGraphDecode lower length positive lengthPositive
          largerAngular largerCell largerInserted field).val 0 := by
      rw [annularOmegaGraphDecode_zero, annularOmegaGraphDecode_zero]
      change annularLpDecode angular cell inserted
        ((annularOmegaGraphDiagonal lower length positive lengthPositive
          (fun mode => annularGradeWeight angular cell inserted mode /
            annularGradeWeight largerAngular largerCell largerInserted mode)
          1 (by norm_num)
          (annularGradeWeight_ratio_bound angular cell inserted largerAngular largerCell largerInserted
            angularLe cellLe insertedLe) field).val 0) = _
      rw [annularOmegaGraphDiagonal_value]
      exact annularLpGradeInclusion_decode angular cell inserted largerAngular largerCell largerInserted
        angularLe cellLe insertedLe (field.val 0)
    simpa using result
  · have result :
        (annularOmegaGraphDecode lower length positive lengthPositive angular cell inserted
          (annularOmegaGradeInclusion lower length positive lengthPositive angular cell inserted
            largerAngular largerCell largerInserted angularLe cellLe insertedLe field)).val 1 =
        (annularOmegaGraphDecode lower length positive lengthPositive
          largerAngular largerCell largerInserted field).val 1 := by
      rw [annularOmegaGraphDecode_one, annularOmegaGraphDecode_one]
      change annularLpDecode angular cell inserted
        ((annularOmegaGraphDiagonal lower length positive lengthPositive
          (fun mode => annularGradeWeight angular cell inserted mode /
            annularGradeWeight largerAngular largerCell largerInserted mode)
          1 (by norm_num)
          (annularGradeWeight_ratio_bound angular cell inserted largerAngular largerCell largerInserted
            angularLe cellLe insertedLe) field).val 1) = _
      rw [annularOmegaGraphDiagonal_slope]
      exact annularLpGradeInclusion_decode angular cell inserted largerAngular largerCell largerInserted
        angularLe cellLe insertedLe (field.val 1)
    simpa using result

theorem annularOmegaGradeInclusion_injective :
    Function.Injective
      (annularOmegaGradeInclusion lower length positive lengthPositive angular cell inserted
        largerAngular largerCell largerInserted angularLe cellLe insertedLe) := by
  intro first second equality
  apply annularOmegaGraphDecode_injective lower length positive lengthPositive
    largerAngular largerCell largerInserted
  exact (annularOmegaGradeInclusion_decode lower length positive lengthPositive angular cell inserted
    largerAngular largerCell largerInserted angularLe cellLe insertedLe first).symm.trans
      ((congrArg (annularOmegaGraphDecode lower length positive lengthPositive angular cell inserted)
        equality).trans
        (annularOmegaGradeInclusion_decode lower length positive lengthPositive angular cell inserted
          largerAngular largerCell largerInserted angularLe cellLe insertedLe second))

include angularLe cellLe insertedLe in
theorem HasAnnularOmegaGrade.mono
    (field : annularOmegaGraph lower length positive lengthPositive)
    (grade : HasAnnularOmegaGrade lower largerAngular largerCell largerInserted field.val) :
    HasAnnularOmegaGrade lower angular cell inserted field.val := by
  let weighted := annularOmegaWeightedGraph lower length positive lengthPositive
    largerAngular largerCell largerInserted field grade
  have decoded := annularOmegaGradeInclusion_decode lower length positive lengthPositive angular cell inserted
    largerAngular largerCell largerInserted angularLe cellLe insertedLe weighted
  have identity := decoded.trans
    (annularOmegaGraphDecode_weighted lower length positive lengthPositive
      largerAngular largerCell largerInserted field grade)
  exact (congrArg (fun output : annularOmegaGraph lower length positive lengthPositive =>
    HasAnnularOmegaGrade lower angular cell inserted output.val) identity).mp
      (annularOmegaGraphDecode_hasGrade lower length positive lengthPositive angular cell inserted
        (annularOmegaGradeInclusion lower length positive lengthPositive angular cell inserted
          largerAngular largerCell largerInserted angularLe cellLe insertedLe weighted))

/-- AAQ14's diagonal on Dnu is exactly the normalization of the natural
Domega grade inclusion. -/
theorem annularOmegaNormalization_gradeInclusion
    (field : annularOmegaGraph lower length positive lengthPositive) :
    annularOmegaNormalizationEquivalence lower length positive lengthPositive
      (annularOmegaGradeInclusion lower length positive lengthPositive angular cell inserted
        largerAngular largerCell largerInserted angularLe cellLe insertedLe field) =
    annularFluxGraphDiagonal lower positive
      (fun mode => annularGradeWeight angular cell inserted mode /
        annularGradeWeight largerAngular largerCell largerInserted mode)
      1 (by norm_num)
      (annularGradeWeight_ratio_bound angular cell inserted largerAngular largerCell largerInserted
        angularLe cellLe insertedLe)
      (annularOmegaNormalizationEquivalence lower length positive lengthPositive field) := by
  simpa only [annularOmegaGradeInclusion] using
    annularOmegaNormalization_diagonal lower length positive lengthPositive
      (fun mode => annularGradeWeight angular cell inserted mode /
        annularGradeWeight largerAngular largerCell largerInserted mode)
      1 (by norm_num)
      (annularGradeWeight_ratio_bound angular cell inserted largerAngular largerCell largerInserted
        angularLe cellLe insertedLe) field

end Inclusion

theorem annularOmegaGradeInclusion_refl (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (angular cell inserted : ℕ)
    (field : annularOmegaGraph lower length positive lengthPositive) :
    annularOmegaGradeInclusion lower length positive lengthPositive angular cell inserted
      angular cell inserted le_rfl le_rfl le_rfl field = field := by
  apply annularOmegaGraphDecode_injective lower length positive lengthPositive angular cell inserted
  exact annularOmegaGradeInclusion_decode lower length positive lengthPositive angular cell inserted
    angular cell inserted le_rfl le_rfl le_rfl field

/-- The literal Domega inclusions form one coherent tower across every
angular/cell split and inserted grade. -/
theorem annularOmegaGradeInclusion_trans (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length)
    (a₀ c₀ i₀ a₁ c₁ i₁ a₂ c₂ i₂ : ℕ)
    (a01 : a₀ ≤ a₁) (c01 : c₀ ≤ c₁) (i01 : i₀ ≤ i₁)
    (a12 : a₁ ≤ a₂) (c12 : c₁ ≤ c₂) (i12 : i₁ ≤ i₂)
    (field : annularOmegaGraph lower length positive lengthPositive) :
    annularOmegaGradeInclusion lower length positive lengthPositive a₀ c₀ i₀ a₁ c₁ i₁ a01 c01 i01
      (annularOmegaGradeInclusion lower length positive lengthPositive a₁ c₁ i₁ a₂ c₂ i₂
        a12 c12 i12 field) =
    annularOmegaGradeInclusion lower length positive lengthPositive a₀ c₀ i₀ a₂ c₂ i₂
      (a01.trans a12) (c01.trans c12) (i01.trans i12) field := by
  apply annularOmegaGraphDecode_injective lower length positive lengthPositive a₀ c₀ i₀
  have first := annularOmegaGradeInclusion_decode lower length positive lengthPositive
    a₀ c₀ i₀ a₁ c₁ i₁ a01 c01 i01
    (annularOmegaGradeInclusion lower length positive lengthPositive a₁ c₁ i₁ a₂ c₂ i₂
      a12 c12 i12 field)
  have second := annularOmegaGradeInclusion_decode lower length positive lengthPositive
    a₁ c₁ i₁ a₂ c₂ i₂ a12 c12 i12 field
  have direct := annularOmegaGradeInclusion_decode lower length positive lengthPositive
    a₀ c₀ i₀ a₂ c₂ i₂ (a01.trans a12) (c01.trans c12) (i01.trans i12) field
  exact first.trans (second.trans direct.symm)

/-- Final exact grade consumer for the literal original Domega graph:
both physical coordinates are weighted, the realization is the range of
one injective decode, and the reciprocal Dnu model has exactly the same grade. -/
theorem annularOriginalOmegaGrades_consumer (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (angular cell inserted : ℕ)
    (field : annularOmegaGraph lower length positive lengthPositive) :
    HasAnnularOmegaGrade lower angular cell inserted field.val ↔
      HasAnnularFluxGrade lower positive angular cell inserted
          (annularOmegaNormalizationEquivalence lower length positive lengthPositive field) ∧
        ∃ weighted : annularOmegaGraph lower length positive lengthPositive,
          annularOmegaGraphDecode lower length positive lengthPositive angular cell inserted weighted = field := by
  constructor
  · intro grade
    exact ⟨(annularOmegaGrade_iff_fluxGrade lower length positive lengthPositive
      angular cell inserted field).mp grade,
      (annularOmegaGraphGrade_iff lower length positive lengthPositive angular cell inserted field).mp grade⟩
  · rintro ⟨_, weighted⟩
    exact (annularOmegaGraphGrade_iff lower length positive lengthPositive angular cell inserted field).mpr weighted

end Grad.AnnularOmegaGraph
