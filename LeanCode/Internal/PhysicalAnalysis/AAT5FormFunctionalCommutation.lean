import AAT4TraceLiftCommutation

noncomputable section
set_option maxHeartbeats 1000000

namespace Grad.AnnularGrades

open Grad.AnnularVariational Grad.AnnularReconstruction Grad.CartesianState

section Data
variable (lower : ℝ) (coefficient : HighAnnularMode → ℝ) (constant : ℝ)
    (nonnegative : 0 ≤ constant) (bounded : ∀ index, |coefficient index| ≤ constant)

def annularForcingDiagonal : AnnularForcing lower →L[ℂ] AnnularForcing lower :=
  (realLpDiagonal coefficient constant nonnegative bounded).prodMap
    ((realLpDiagonal coefficient constant nonnegative bounded).prodMap
      ((realLpDiagonal coefficient constant nonnegative bounded).prodMap
        (realLpDiagonal coefficient constant nonnegative bounded)))

def annularDataDiagonal : (AnnularForcing lower × AnnularBoundary) →L[ℂ]
    (AnnularForcing lower × AnnularBoundary) :=
  (annularForcingDiagonal lower coefficient constant nonnegative bounded).prodMap
    (realLpDiagonal coefficient constant nonnegative bounded)

end Data

section Commutation
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (coefficient : HighAnnularMode → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index, |coefficient index| ≤ constant)

/-- The actual scalar form is diagonal, including the original phase
cross terms and the original energy outer term. -/
theorem annularFormValue_diagonal (field test : annularEnergySpace lower length positive) :
    annularFormValue parameters lower length positive lengthPositive widthHalf widthLength
      (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded field) test =
        annularFormValue parameters lower length positive lengthPositive widthHalf widthLength field
          (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded test) := by
  simp only [annularFormValue, annularEnergyPhase_diagonal, annularEnergyDerivative_diagonal,
    ← annularEnergyDiagonal_adjoint, ← realLpDiagonal_adjoint]

theorem annularSourceTest_diagonal (test : annularEnergySpace lower length positive) :
    annularSourceTest parameters lower length positive lengthPositive widthHalf widthLength
      (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded test) =
        realLpDiagonal coefficient constant nonnegative bounded
          (annularSourceTest parameters lower length positive lengthPositive widthHalf widthLength test) := by
  simp only [annularSourceTest, add_apply, annularEnergyDerivative_diagonal,
    annularEnergyPhase_diagonal, annularEnergyRadial_diagonal, map_add]

/-- All undifferentiated sources and the natural outer datum use the same
Fourier scalar; no derivative or trace of a bulk source is introduced. -/
theorem annularFunctionalValue_diagonal (source : AnnularForcing lower)
    (test : annularEnergySpace lower length positive) :
    annularFunctionalValue parameters lower length positive collar lengthPositive widthHalf widthLength
      (annularForcingDiagonal lower coefficient constant nonnegative bounded source) test =
        annularFunctionalValue parameters lower length positive collar lengthPositive widthHalf widthLength source
          (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded test) := by
  change inner ℂ (annularSourceTest parameters lower length positive lengthPositive widthHalf widthLength test)
      (realLpDiagonal coefficient constant nonnegative bounded source.1) -
    inner ℂ (annularEnergyD lower length positive test) (realLpDiagonal coefficient constant nonnegative bounded source.2.1) -
    inner ℂ (annularEnergyCell lower length positive test) (realLpDiagonal coefficient constant nonnegative bounded source.2.2.1) -
    inner ℂ (annularEnergyTrace lower length positive collar lengthPositive 1 test)
      (realLpDiagonal coefficient constant nonnegative bounded source.2.2.2) = _
  simp only [annularFunctionalValue, annularSourceTest_diagonal, annularEnergyD_diagonal,
    annularEnergyCell_diagonal, annularEnergyTrace_diagonal, ← realLpDiagonal_adjoint]

end Commutation

end Grad.AnnularGrades
