import GC17FrameInverse

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation

theorem actualInverseInput_margins {L ell radius threshold : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold)
    (rho alpha delta parameter epsilon : ℝ)
    (rhoSmall : |rho| ≤ 1) (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) (epsilonSmall : |epsilon| ≤ 1)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ ledgerLowRadius parameters L radius threshold) :
    physicalBudget parameters field rho epsilon 4 ≤ 1 ∧
      ‖frameInverseInput parameters admissible epsilon field 0‖ ≤ 1 / 4 ∧
      ‖seedInverseInput admissible rho alpha delta parameter 0‖ ≤ 1 / 4 := by
  have primitive := (primitiveSize_low_margin parameters admissible radiusNonnegative thresholdPositive
    rho alpha delta parameter epsilon rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall field low).2
  change ‖actualFrameFamily parameters L ell epsilon field 0‖ +
    ‖seedMatrixDeviationCoefficient admissible 0 rho alpha delta parameter‖ +
    ‖seedDerivativeCoefficient admissible 0 rho alpha delta parameter‖ ≤ 1 / 4 at primitive
  refine ⟨(physicalBudget_monotone parameters field rho epsilon (by norm_num : 4 ≤ 6)).trans
    (low.trans (ledgerLowRadius_le_one parameters L radius threshold)), ?_, ?_⟩
  · apply (frameInverseInput_base_le parameters admissible epsilon field).trans
    linarith [norm_nonneg (seedMatrixDeviationCoefficient admissible 0 rho alpha delta parameter),
      norm_nonneg (seedDerivativeCoefficient admissible 0 rho alpha delta parameter)]
  · change ‖-seedMatrixDeviationCoefficient admissible 0 rho alpha delta parameter‖ ≤ _
    rw [norm_neg]
    linarith [norm_nonneg (actualFrameFamily parameters L ell epsilon field 0),
      norm_nonneg (seedDerivativeCoefficient admissible 0 rho alpha delta parameter)]

def actualSeedInverse {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (rho alpha delta parameter : ℝ) : CoefficientFamily L sigma gamma ell 2 2 :=
  inverseFamily admissible (seedInverseInput admissible rho alpha delta parameter)

theorem actualSeedInverse_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (rho alpha delta parameter : ℝ)
    (baseBound : ‖seedInverseInput admissible rho alpha delta parameter 0‖ ≤ 1 / 4) :
    FamilyCoherent (actualSeedInverse admissible rho alpha delta parameter) :=
  inverseFamily_coherent admissible (by norm_num : 0 < 2) _
    (seedInverseInput_coherent admissible rho alpha delta parameter) (1 / 4) baseBound (by norm_num)

def seedInverseDeviationConstant (sigma radius : ℝ) (grade : ℕ) : ℝ :=
  inverseNormConstant (seedDeviationConstant sigma radius) 4 grade 1 (1 / 4)

theorem seedInverseDeviationConstant_nonnegative (sigma radius : ℝ) (grade : ℕ) :
    0 ≤ seedInverseDeviationConstant sigma radius grade :=
  inverseNormConstant_nonnegative _ (seedDeviationConstant_nonnegative sigma radius) 4 grade
    (by norm_num : 0 ≤ (1 : ℝ)) (by norm_num : (1 / 4 : ℝ) < 1)

theorem actualSeedInverse_deviation_bound {L ell radius : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (radiusNonnegative : 0 ≤ radius) (rho alpha delta parameter epsilon : ℝ)
    (rhoSmall : |rho| ≤ 1) (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 4 ≤ 1)
    (baseBound : ‖seedInverseInput admissible rho alpha delta parameter 0‖ ≤ 1 / 4) (grade : ℕ) :
    ‖actualSeedInverse admissible rho alpha delta parameter grade -
      gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade 2‖ ≤
        seedInverseDeviationConstant parameters.sigma0 radius grade *
          physicalBudget parameters field rho epsilon (4 + grade) :=
  inverse_norm_one_high parameters admissible 4 grade field rho epsilon 1 (1 / 4)
    (by norm_num) (by norm_num) low (by norm_num : 0 < 2)
    (seedInverseInput admissible rho alpha delta parameter)
    (seedInverseInput_coherent admissible rho alpha delta parameter)
    (seedDeviationConstant parameters.sigma0 radius) (seedDeviationConstant_nonnegative parameters.sigma0 radius)
    (seedInverseInput_bound parameters admissible radiusNonnegative rho alpha delta parameter epsilon
      rhoSmall alphaSmall deltaSmall parameterSmall field) baseBound

theorem actualSeedInverse_two_sided {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (rho alpha delta parameter : ℝ)
    (baseBound : ‖seedInverseInput admissible rho alpha delta parameter 0‖ ≤ 1 / 4)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    let inverse := coefficientPhysicalValue (actualSeedInverse admissible rho alpha delta parameter grade) angle point
    (harmonicSeedOperator rho alpha delta parameter angle).comp inverse =
        ContinuousLinearMap.id ℂ (PhysicalValue 2) ∧
      inverse.comp (harmonicSeedOperator rho alpha delta parameter angle) =
        ContinuousLinearMap.id ℂ (PhysicalValue 2) := by
  dsimp only
  unfold actualSeedInverse
  rw [inverseFamily_physicalValue admissible (by norm_num : 0 < 2) _
    (seedInverseInput_coherent admissible rho alpha delta parameter) (1 / 4) baseBound (by norm_num)]
  have identities := analyticCapCoefficientNeumannInverse_pointwiseIdentification admissible
    (by norm_num : 0 < 2) (seedInverseInput admissible rho alpha delta parameter 0)
    (1 / 4) baseBound (by norm_num) angle point
  rw [seedInverseInput_fourier] at identities
  exact identities

end Grad.GaugeCoefficients.Physical.Ledger
