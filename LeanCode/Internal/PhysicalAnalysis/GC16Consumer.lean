import GC16Proof

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.InverseAllocation

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

theorem oneHighInverseBlock : OneHighInverseGoal := oneHighInverseGoal

/-- H = -(M-I), with M the prescribed harmonic seed. Thus I-H is literally M. -/
def seedInverseInput {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (rho alpha delta parameter : ℝ) : CoefficientFamily L sigma gamma ell 2 2 :=
  fun grade => -seedMatrixDeviationCoefficient admissible grade rho alpha delta parameter

theorem seedInverseInput_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (rho alpha delta parameter : ℝ) :
    FamilyCoherent (seedInverseInput admissible rho alpha delta parameter) := by
  have seedCoherent : FamilyCoherent
      (fun grade => seedMatrixDeviationCoefficient admissible grade rho alpha delta parameter) := by
    intro firstGrade secondGrade first second same cell point
    rw [seedMatrixDeviation_derivative, seedMatrixDeviation_derivative]
    have orderSame : derivativeOrder first = derivativeOrder second := congrArg cartesianOrder same
    rw [orderSame]
  unfold seedInverseInput
  simpa only [neg_one_smul] using seedCoherent.smul (-1 : ℂ)

theorem seedInverseInput_bound {L ell radius : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (radiusNonnegative : 0 ≤ radius) (rho alpha delta parameter epsilon : ℝ)
    (rhoSmall : |rho| ≤ 1) (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) (field : ACore parameters 3) (grade : ℕ) :
    ‖seedInverseInput admissible rho alpha delta parameter grade‖ ≤
      seedDeviationConstant parameters.sigma0 radius grade *
        physicalBudget parameters field rho epsilon (4 + grade) := by
  change ‖-seedMatrixDeviationCoefficient admissible grade rho alpha delta parameter‖ ≤ _
  rw [norm_neg]
  apply (seedMatrixDeviation_norm_le admissible grade radiusNonnegative rhoSmall alphaSmall deltaSmall parameterSmall).trans
  apply mul_le_mul_of_nonneg_left _ (seedDeviationConstant_nonnegative parameters.sigma0 radius grade)
  unfold physicalBudget
  linarith [Grad.NonlinearProduct.originalGradeNorm_nonnegative (4 + grade) field, abs_nonneg epsilon]

theorem seedInverseInput_base_margin {L ell radius : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (radiusNonnegative : 0 ≤ radius) (rho alpha delta parameter epsilon : ℝ)
    (rhoSmall : |rho| ≤ 1) (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) (epsilonSmall : |epsilon| ≤ 1)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 10 ≤ actualPrimitiveLowRadius parameters L radius) :
    ‖seedInverseInput admissible rho alpha delta parameter 0‖ ≤ 1 / 4 := by
  have lowOriginal : stateBudget parameters (GradeCore.ofCoreLinear (grade := 10) field) rho epsilon ≤
      actualPrimitiveLowRadius parameters L radius := low
  have margin := actualPrimitive_low_margin parameters admissible radiusNonnegative rho alpha delta parameter epsilon
    rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall field lowOriginal
  change ‖actualFrameDeviationCoefficient parameters L ell epsilon
      (GradeCore.ofCoreLinear (grade := 4) field)‖ +
    ‖seedMatrixDeviationCoefficient admissible 0 rho alpha delta parameter‖ +
    ‖seedDerivativeCoefficient admissible 0 rho alpha delta parameter‖ ≤ 1 / 4 at margin
  change ‖-seedMatrixDeviationCoefficient admissible 0 rho alpha delta parameter‖ ≤ _
  rw [norm_neg]
  linarith [norm_nonneg (actualFrameDeviationCoefficient parameters L ell epsilon
    (GradeCore.ofCoreLinear (grade := 4) field)),
    norm_nonneg (seedDerivativeCoefficient admissible 0 rho alpha delta parameter)]

theorem seedInverseInput_fourier {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (rho alpha delta parameter angle : ℝ) (point : ClosedDisk) :
    ContinuousLinearMap.id ℂ (PhysicalValue 2) -
        fourierEvaluation (seedInverseInput admissible rho alpha delta parameter 0) angle point =
      harmonicSeedOperator rho alpha delta parameter angle := by
  change ContinuousLinearMap.id ℂ (PhysicalValue 2) -
      seedFourierCLM admissible 2 2 angle point
        (-seedMatrixDeviationCoefficient admissible 0 rho alpha delta parameter) = _
  rw [map_neg]
  change ContinuousLinearMap.id ℂ (PhysicalValue 2) -
      (-fourierEvaluation (seedMatrixDeviationCoefficient admissible 0 rho alpha delta parameter) angle point) = _
  rw [seedMatrixDeviation_fourier admissible]
  abel

/-- Genuine physical consumer: the actual harmonic seed inverse on the
already accepted primitive B10 ball, with no new radius and no high-grade
smallness. Constants depend only on fixed parameters, patch and grade. -/
theorem actual_seed_inverse_one_high {L ell radius : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (radiusNonnegative : 0 ≤ radius) (rho alpha delta parameter epsilon : ℝ)
    (rhoSmall : |rho| ≤ 1) (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) (epsilonSmall : |epsilon| ≤ 1)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 10 ≤ actualPrimitiveLowRadius parameters L radius)
    (grade : ℕ) :
    ‖inverseFamily admissible (seedInverseInput admissible rho alpha delta parameter) grade -
      gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade 2‖ ≤
        inverseNormConstant (seedDeviationConstant parameters.sigma0 radius) 4 grade
          (actualPrimitiveLowRadius parameters L radius) (1 / 4) *
            physicalBudget parameters field rho epsilon (grade + 4) := by
  have lowFour := (physicalBudget_monotone parameters field rho epsilon (by norm_num : 4 ≤ 10)).trans low
  have baseMargin := seedInverseInput_base_margin parameters admissible radiusNonnegative rho alpha delta parameter epsilon
    rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall field low
  have bound := inverse_norm_one_high parameters admissible 4 grade field rho epsilon
    (actualPrimitiveLowRadius parameters L radius) (1 / 4)
    (actualPrimitiveLowRadius_positive parameters admissible.1 radius).le (by norm_num) lowFour
    (by norm_num : 0 < 2) (seedInverseInput admissible rho alpha delta parameter)
    (seedInverseInput_coherent admissible rho alpha delta parameter) (seedDeviationConstant parameters.sigma0 radius)
    (seedDeviationConstant_nonnegative parameters.sigma0 radius)
    (seedInverseInput_bound parameters admissible radiusNonnegative rho alpha delta parameter epsilon
      rhoSmall alphaSmall deltaSmall parameterSmall field) baseMargin
  simpa only [Nat.add_comm 4 grade] using bound

theorem actual_seed_inverse_two_sided {L ell radius : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (radiusNonnegative : 0 ≤ radius) (rho alpha delta parameter epsilon : ℝ)
    (rhoSmall : |rho| ≤ 1) (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) (epsilonSmall : |epsilon| ≤ 1)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 10 ≤ actualPrimitiveLowRadius parameters L radius)
    (angle : ℝ) (point : ClosedDisk) :
    let inverse := fourierEvaluation
      (analyticCapCoefficientNeumannInverse admissible (seedInverseInput admissible rho alpha delta parameter 0)) angle point
    (harmonicSeedOperator rho alpha delta parameter angle).comp inverse = ContinuousLinearMap.id ℂ (PhysicalValue 2) ∧
      inverse.comp (harmonicSeedOperator rho alpha delta parameter angle) = ContinuousLinearMap.id ℂ (PhysicalValue 2) := by
  have baseMargin := seedInverseInput_base_margin parameters admissible radiusNonnegative rho alpha delta parameter epsilon
    rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall field low
  have identities := analyticCapCoefficientNeumannInverse_pointwiseIdentification admissible (by norm_num : 0 < 2)
    (seedInverseInput admissible rho alpha delta parameter 0) (1 / 4) baseMargin (by norm_num) angle point
  rw [seedInverseInput_fourier] at identities
  exact identities

end Grad.GaugeCoefficients.Physical.InverseAllocation
