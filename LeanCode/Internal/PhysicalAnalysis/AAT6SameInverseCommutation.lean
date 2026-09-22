import AAT5FormFunctionalCommutation

noncomputable section
set_option maxHeartbeats 1000000

namespace Grad.AnnularGrades

open Grad.AnnularVariational Grad.CartesianState

section Inverse
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (coefficient : HighAnnularMode → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index, |coefficient index| ≤ constant)

/-- The SAME actual solution commutes with every bounded real Fourier
multiplier. This follows from the original weak equation and uniqueness,
not from assuming an independently defined graded inverse. -/
theorem annularVariationalSolution_diagonal (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded
      (annularVariationalSolution parameters lower length positive collar lengthPositive widthHalf widthLength source innerValue) =
        annularVariationalSolution parameters lower length positive collar lengthPositive widthHalf widthLength
          (annularForcingDiagonal lower coefficient constant nonnegative bounded source)
          (realLpDiagonal coefficient constant nonnegative bounded innerValue) := by
  apply annularVariationalSolution_unique parameters lower length positive collar lengthPositive widthHalf widthLength
  · rw [annularEnergyTrace_diagonal, annularVariationalSolution_inner]
  · intro test
    have law := annularVariationalSolution_weak parameters lower length positive collar lengthPositive widthHalf widthLength
      source innerValue (annularZeroDiagonal lower length positive collar lengthPositive coefficient constant nonnegative bounded test)
    exact (annularFormValue_diagonal parameters lower length positive lengthPositive widthHalf widthLength
      coefficient constant nonnegative bounded _ test.val).trans
      (law.trans (annularFunctionalValue_diagonal parameters lower length positive collar lengthPositive widthHalf widthLength
        coefficient constant nonnegative bounded source test.val).symm)

theorem annularVariationalInverse_diagonal (data : AnnularForcing lower × AnnularBoundary) :
    annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded
      (annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data) =
        annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength
          (annularDataDiagonal lower coefficient constant nonnegative bounded data) :=
  annularVariationalSolution_diagonal parameters lower length positive collar lengthPositive widthHalf widthLength
    coefficient constant nonnegative bounded data.1 data.2

end Inverse

end Grad.AnnularGrades
