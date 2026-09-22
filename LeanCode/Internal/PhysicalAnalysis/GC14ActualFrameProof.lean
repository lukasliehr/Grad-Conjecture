import GC14SeedDerivativeFourier

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

theorem seedMatrixDeviation_derivative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (rho alpha delta parameter : ℝ)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (seedMatrixDeviationCoefficient admissible grade rho alpha delta parameter)
        cell index point =
      if derivativeOrder index = 0 then seedDeviationCell rho alpha delta parameter cell else 0 := by
  by_cases zeroOrder : derivativeOrder index = 0
  · rw [if_pos zeroOrder]
    have zeroIndex : index = Grad.GaugeCoefficients.Neumann.Regularity.zeroDerivativeIndexAt grade := by
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      all_goals change _ = 0
      all_goals unfold derivativeOrder at zeroOrder
      all_goals omega
    rw [zeroIndex]
    exact seedMatrixDeviation_cell admissible grade rho alpha delta parameter cell point
  · rw [if_neg zeroOrder]
    exact seedMatrixDeviation_spatial admissible grade rho alpha delta parameter
      cell index (Nat.pos_of_ne_zero zeroOrder) point

/-- Literal actual state and harmonic seed coefficients in the original
analytic-width completion, including the exact scaled cell derivative. -/
def actualFrameCoefficients {L ell : ℝ} {grade : ℕ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (field : GradeCore parameters 3 (grade + 4)) :
    ActualFrameCoefficients parameters L ell rho alpha delta parameter epsilon admissible field where
  frameDeviation := actualFrameDeviationCoefficient parameters L ell epsilon field
  seedDeviation := seedMatrixDeviationCoefficient admissible grade rho alpha delta parameter
  seedDerivative := seedDerivativeCoefficient admissible grade rho alpha delta parameter
  frame_value := actualFrameDeviationCoefficient_value parameters admissible epsilon field
  frame_derivative := actualFrameDeviationCoefficient_derivative parameters admissible epsilon field
  seed_derivative := seedMatrixDeviation_derivative admissible grade rho alpha delta parameter
  seed_cell_derivative := seedDerivativeCoefficient_derivative admissible grade rho alpha delta parameter
  seed_fourier := seedValue_fourier admissible rho alpha delta parameter
  seed_derivative_fourier := seedDerivativeValue_fourier admissible rho alpha delta parameter

def actualFrameConstant (parameters : PhaseParameters) (L radius : ℝ) (grade : ℕ) : ℝ :=
  frameConstant parameters L grade + seedDeviationConstant parameters.sigma0 radius grade +
    seedDerivativeConstant parameters.sigma0 radius grade

theorem actualFrameConstant_nonnegative (parameters : PhaseParameters) {L : ℝ} (positive : 0 < L)
    (radius : ℝ) (grade : ℕ) : 0 ≤ actualFrameConstant parameters L radius grade :=
  add_nonneg (add_nonneg (frameConstant_nonnegative parameters positive grade)
    (seedDeviationConstant_nonnegative parameters.sigma0 radius grade))
    (seedDerivativeConstant_nonnegative parameters.sigma0 radius grade)

theorem actualFrameCoefficients_norm_bound {L ell radius : ℝ} {grade : ℕ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (radiusNonnegative : 0 ≤ radius) (rho alpha delta parameter epsilon : ℝ)
    (rhoSmall : |rho| ≤ 1) (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) (epsilonSmall : |epsilon| ≤ 1)
    (field : GradeCore parameters 3 (grade + 4)) :
    let coefficients := actualFrameCoefficients parameters admissible rho alpha delta parameter epsilon field
    ‖coefficients.frameDeviation‖ + ‖coefficients.seedDeviation‖ + ‖coefficients.seedDerivative‖ ≤
      actualFrameConstant parameters L radius grade * stateBudget parameters field rho epsilon := by
  change ‖actualFrameDeviationCoefficient parameters L ell epsilon field‖ +
    ‖seedMatrixDeviationCoefficient admissible grade rho alpha delta parameter‖ +
    ‖seedDerivativeCoefficient admissible grade rho alpha delta parameter‖ ≤ _
  have frame := actualFrameDeviationCoefficient_norm_bound parameters admissible epsilon epsilonSmall field
  have seed := seedMatrixDeviation_norm_le admissible grade radiusNonnegative rhoSmall alphaSmall deltaSmall parameterSmall
  have derivative := seedDerivativeCoefficient_norm_le admissible grade radiusNonnegative rhoSmall alphaSmall deltaSmall parameterSmall
  have framePositive := frameConstant_nonnegative parameters admissible.1 grade
  have seedPositive := seedDeviationConstant_nonnegative parameters.sigma0 radius grade
  have derivativePositive := seedDerivativeConstant_nonnegative parameters.sigma0 radius grade
  calc
    _ ≤ frameConstant parameters L grade * (‖field‖ + |epsilon|) +
        seedDeviationConstant parameters.sigma0 radius grade * |rho| +
        seedDerivativeConstant parameters.sigma0 radius grade * |rho| :=
      add_le_add (add_le_add frame seed) derivative
    _ ≤ _ := by
      unfold actualFrameConstant stateBudget
      nlinarith [mul_nonneg framePositive (abs_nonneg rho),
        mul_nonneg seedPositive (norm_nonneg field), mul_nonneg seedPositive (abs_nonneg epsilon),
        mul_nonneg derivativePositive (norm_nonneg field), mul_nonneg derivativePositive (abs_nonneg epsilon)]

/-- AP20–AP21 actual construction: no supplied analytic frame or seed
coefficient assumption, no auxiliary-width loss, and the exact `q+4` state grade. -/
theorem actualFrameGoal : ActualFrameGoal := by
  intro parameters L radius positive radiusNonnegative grade
  refine ⟨actualFrameConstant parameters L radius grade,
    actualFrameConstant_nonnegative parameters positive radius grade, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall field _reality
  exact ⟨actualFrameCoefficients parameters admissible rho alpha delta parameter epsilon field,
    actualFrameCoefficients_norm_bound parameters admissible radiusNonnegative rho alpha delta parameter epsilon
      rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall field⟩

end Grad.GaugeCoefficients.Physical.Frame
