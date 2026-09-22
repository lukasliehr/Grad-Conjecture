import AAT10NormalizedGradeCoordinates

noncomputable section
set_option maxHeartbeats 1000000

namespace Grad.AnnularGrades

open Grad.AnnularVariational Grad.CartesianState

/-- Literal weighted square summability of all four physical forcing
coordinates and the independently prescribed sharp inner datum. -/
def HasAnnularDataGrade (lower : ℝ) (angular cell inserted : ℕ)
    (data : AnnularForcing lower × AnnularBoundary) : Prop :=
  HasAnnularLpGrade angular cell inserted data.1.1 ∧
  HasAnnularLpGrade angular cell inserted data.1.2.1 ∧
  HasAnnularLpGrade angular cell inserted data.1.2.2.1 ∧
  HasAnnularLpGrade angular cell inserted data.1.2.2.2 ∧
  HasAnnularLpGrade angular cell inserted data.2

def annularWeightedData (lower : ℝ) (angular cell inserted : ℕ)
    (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data) : AnnularForcing lower × AnnularBoundary :=
  ((annularLpWeighted angular cell inserted data.1.1 grade.1,
      (annularLpWeighted angular cell inserted data.1.2.1 grade.2.1,
        (annularLpWeighted angular cell inserted data.1.2.2.1 grade.2.2.1,
          annularLpWeighted angular cell inserted data.1.2.2.2 grade.2.2.2.1))),
    annularLpWeighted angular cell inserted data.2 grade.2.2.2.2)

def annularDataDecode (lower : ℝ) (angular cell inserted : ℕ) :
    (AnnularForcing lower × AnnularBoundary) →L[ℂ] (AnnularForcing lower × AnnularBoundary) :=
  annularDataDiagonal lower (fun mode => (annularGradeWeight angular cell inserted mode)⁻¹)
    1 (by norm_num) (annularGradeWeight_inv_bound angular cell inserted)

theorem annularDataDecode_weighted (lower : ℝ) (angular cell inserted : ℕ)
    (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data) :
    annularDataDecode lower angular cell inserted (annularWeightedData lower angular cell inserted data grade) = data := by
  change ((annularLpDecode angular cell inserted (annularLpWeighted angular cell inserted data.1.1 grade.1),
      (annularLpDecode angular cell inserted (annularLpWeighted angular cell inserted data.1.2.1 grade.2.1),
        (annularLpDecode angular cell inserted (annularLpWeighted angular cell inserted data.1.2.2.1 grade.2.2.1),
          annularLpDecode angular cell inserted (annularLpWeighted angular cell inserted data.1.2.2.2 grade.2.2.2.1)))),
    annularLpDecode angular cell inserted (annularLpWeighted angular cell inserted data.2 grade.2.2.2.2)) = data
  simp only [annularLpDecode_weighted]

section Inverse
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (angular cell inserted : ℕ)

theorem annularInverse_decoded_weighted (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data) :
    annularEnergyDecode lower length positive angular cell inserted
      (annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength
        (annularWeightedData lower angular cell inserted data grade)) =
      annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data :=
  (annularVariationalInverse_diagonal parameters lower length positive collar lengthPositive widthHalf widthLength
    (fun mode => (annularGradeWeight angular cell inserted mode)⁻¹) 1 (by norm_num)
    (annularGradeWeight_inv_bound angular cell inserted) (annularWeightedData lower angular cell inserted data grade)).trans
      (congrArg (fun input => annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength input)
        (annularDataDecode_weighted lower angular cell inserted data grade))

/-- Actual weighted regularity of the SAME original-width inverse. -/
theorem annularInverse_hasGrade (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data) :
    HasAnnularEnergyGrade lower length positive angular cell inserted
      (annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data) :=
  (congrArg (HasAnnularEnergyGrade lower length positive angular cell inserted)
    (annularInverse_decoded_weighted parameters lower length positive collar lengthPositive widthHalf widthLength
      angular cell inserted data grade)).mp
    (annularEnergyDecode_hasGrade lower length positive angular cell inserted
      (annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength
        (annularWeightedData lower angular cell inserted data grade)))

theorem annularInverse_weighted_identity (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data)
    (solutionGrade : HasAnnularEnergyGrade lower length positive angular cell inserted
      (annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data)) :
    annularWeightedEnergy lower length positive angular cell inserted
      (annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data) solutionGrade =
      annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength
        (annularWeightedData lower angular cell inserted data grade) := by
  apply annularEnergyDecode_injective lower length positive angular cell inserted
  exact (annularEnergyDecode_weighted lower length positive angular cell inserted _ solutionGrade).trans
    (annularInverse_decoded_weighted parameters lower length positive collar lengthPositive widthHalf widthLength
      angular cell inserted data grade).symm

/-- The exact base energy constant works at every split and inserted grade. -/
theorem annularInverse_weighted_bound (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data)
    (solutionGrade : HasAnnularEnergyGrade lower length positive angular cell inserted
      (annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data)) :
    ‖annularWeightedEnergy lower length positive angular cell inserted
      (annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data) solutionGrade‖ ≤
      annularInnerLiftConstant lower length * ‖(annularWeightedData lower angular cell inserted data grade).2‖ +
        (4 / 3 : ℝ) * (annularForcingSize lower length (annularWeightedData lower angular cell inserted data grade).1 +
          4 * annularInnerLiftConstant lower length * ‖(annularWeightedData lower angular cell inserted data grade).2‖) := by
  rw [annularInverse_weighted_identity parameters lower length positive collar lengthPositive widthHalf widthLength
    angular cell inserted data grade solutionGrade]
  exact annularVariationalSolution_bound parameters lower length positive collar lengthPositive widthHalf widthLength _ _

end Inverse

end Grad.AnnularGrades
