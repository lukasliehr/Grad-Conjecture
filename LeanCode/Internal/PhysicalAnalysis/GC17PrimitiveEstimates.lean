import GC17EstimateAlgebra
import GC17RotatedFrame

noncomputable section

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation

def identityFamily (L sigma gamma ell : ℝ) (dimension : ℕ) : CoefficientFamily L sigma gamma ell dimension dimension :=
  fun grade => gradedIdentityCoefficient L sigma gamma ell grade dimension

theorem identityFamily_norm_le (L sigma gamma ell : ℝ) (dimension grade : ℕ) :
    ‖identityFamily L sigma gamma ell dimension grade‖ ≤ Fintype.card (DerivativeIndex grade) := by
  rw [norm_eq_topSlot_sum]
  calc
    _ ≤ ∑ _ : DerivativeIndex grade, (1 : ℝ) :=
      Finset.sum_le_sum fun index _ => identity_slotNorm_le L sigma gamma ell dimension grade (topSlot index)
    _ = _ := by simp

def fullFrameFamily (parameters : PhaseParameters) (L ell epsilon : ℝ) (field : ACore parameters 3) :
    CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3 :=
  fun grade => constantFamily L parameters.sigma0 parameters.gamma ell referenceFrame grade +
    actualFrameFamily parameters L ell epsilon field grade

def frameProfile (parameters : PhaseParameters) (L : ℝ) : EstimateProfile :=
  ⟨fixedFamilyConstant referenceFrame, frameConstant parameters L⟩

theorem fullFrameFamily_estimate {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho epsilon : ℝ) (epsilonSmall : |epsilon| ≤ 1) (field : ACore parameters 3) :
    FamilyEstimate parameters field rho epsilon 4 (frameProfile parameters L)
      (fullFrameFamily parameters L ell epsilon field)
      (constantFamily L parameters.sigma0 parameters.gamma ell referenceFrame) where
  actualCoherent := (constantFamily_coherent L parameters.sigma0 parameters.gamma ell referenceFrame).add
    (actualFrameFamily_coherent parameters admissible epsilon field)
  referenceCoherent := constantFamily_coherent L parameters.sigma0 parameters.gamma ell referenceFrame
  fixedNonnegative := fixedFamilyConstant_nonnegative referenceFrame
  deviationNonnegative := frameConstant_nonnegative parameters admissible.1
  referenceBound := constantFamily_norm_le admissible referenceFrame
  deviationBound grade := by
    change ‖(constantFamily L parameters.sigma0 parameters.gamma ell referenceFrame grade +
      actualFrameFamily parameters L ell epsilon field grade) -
        constantFamily L parameters.sigma0 parameters.gamma ell referenceFrame grade‖ ≤ _
    rw [add_sub_cancel_left]
    exact actualFrameFamily_bound parameters admissible epsilon rho epsilonSmall field grade

def inverseFrameProfile (parameters : PhaseParameters) (L : ℝ) : EstimateProfile :=
  ⟨fixedFamilyConstant referenceFrame, frameInverseDeviationConstant parameters L⟩

theorem actualFrameInverse_estimate {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho epsilon : ℝ) (epsilonSmall : |epsilon| ≤ 1) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 4 ≤ 1)
    (baseBound : ‖frameInverseInput parameters admissible epsilon field 0‖ ≤ 1 / 4) :
    FamilyEstimate parameters field rho epsilon 4 (inverseFrameProfile parameters L)
      (actualFrameInverse parameters admissible epsilon field)
      (constantFamily L parameters.sigma0 parameters.gamma ell referenceFrame) where
  actualCoherent := actualFrameInverse_coherent parameters admissible epsilon field baseBound
  referenceCoherent := constantFamily_coherent L parameters.sigma0 parameters.gamma ell referenceFrame
  fixedNonnegative := fixedFamilyConstant_nonnegative referenceFrame
  deviationNonnegative := frameInverseDeviationConstant_nonnegative parameters admissible.1
  referenceBound := constantFamily_norm_le admissible referenceFrame
  deviationBound grade := by
    change ‖(constantFamily L parameters.sigma0 parameters.gamma ell referenceFrame grade +
      actualFrameInverseDeviation parameters admissible epsilon field grade) -
        constantFamily L parameters.sigma0 parameters.gamma ell referenceFrame grade‖ ≤ _
    rw [add_sub_cancel_left]
    exact actualFrameInverseDeviation_bound parameters admissible rho epsilon epsilonSmall field low baseBound grade

def seedMatrixFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (rho alpha delta parameter : ℝ) : CoefficientFamily L sigma gamma ell 2 2 :=
  fun grade => gradedIdentityCoefficient L sigma gamma ell grade 2 +
    seedMatrixDeviationCoefficient admissible grade rho alpha delta parameter

theorem seedDeviationFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (rho alpha delta parameter : ℝ) :
    FamilyCoherent (fun grade => seedMatrixDeviationCoefficient admissible grade rho alpha delta parameter) := by
  intro grade other index otherIndex same cell point
  rw [seedMatrixDeviation_derivative, seedMatrixDeviation_derivative]
  rw [show derivativeOrder index = derivativeOrder otherIndex from congrArg cartesianOrder same]

def seedMatrixProfile (sigma radius : ℝ) : EstimateProfile :=
  ⟨fun grade => Fintype.card (DerivativeIndex grade), seedDeviationConstant sigma radius⟩

theorem seedMatrixFamily_estimate {L ell radius : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (radiusNonnegative : 0 ≤ radius) (rho alpha delta parameter epsilon : ℝ)
    (rhoSmall : |rho| ≤ 1) (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) (field : ACore parameters 3) :
    FamilyEstimate parameters field rho epsilon 4 (seedMatrixProfile parameters.sigma0 radius)
      (seedMatrixFamily admissible rho alpha delta parameter) (identityFamily L parameters.sigma0 parameters.gamma ell 2) where
  actualCoherent := (identityFamily_coherent L parameters.sigma0 parameters.gamma ell 2).add
    (seedDeviationFamily_coherent admissible rho alpha delta parameter)
  referenceCoherent := identityFamily_coherent L parameters.sigma0 parameters.gamma ell 2
  fixedNonnegative _ := Nat.cast_nonneg _
  deviationNonnegative := seedDeviationConstant_nonnegative parameters.sigma0 radius
  referenceBound := identityFamily_norm_le L parameters.sigma0 parameters.gamma ell 2
  deviationBound grade := by
    change ‖(gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade 2 +
      seedMatrixDeviationCoefficient admissible grade rho alpha delta parameter) -
        gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade 2‖ ≤ _
    rw [add_sub_cancel_left]
    have bound := seedInverseInput_bound parameters admissible radiusNonnegative rho alpha delta parameter epsilon
      rhoSmall alphaSmall deltaSmall parameterSmall field grade
    change ‖-seedMatrixDeviationCoefficient admissible grade rho alpha delta parameter‖ ≤ _ at bound
    simpa only [norm_neg, seedMatrixProfile] using bound

def inverseSeedProfile (sigma radius : ℝ) : EstimateProfile :=
  ⟨fun grade => Fintype.card (DerivativeIndex grade), seedInverseDeviationConstant sigma radius⟩

theorem actualSeedInverse_estimate {L ell radius : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (radiusNonnegative : 0 ≤ radius) (rho alpha delta parameter epsilon : ℝ)
    (rhoSmall : |rho| ≤ 1) (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 4 ≤ 1)
    (baseBound : ‖seedInverseInput admissible rho alpha delta parameter 0‖ ≤ 1 / 4) :
    FamilyEstimate parameters field rho epsilon 4 (inverseSeedProfile parameters.sigma0 radius)
      (actualSeedInverse admissible rho alpha delta parameter) (identityFamily L parameters.sigma0 parameters.gamma ell 2) where
  actualCoherent := actualSeedInverse_coherent admissible rho alpha delta parameter baseBound
  referenceCoherent := identityFamily_coherent L parameters.sigma0 parameters.gamma ell 2
  fixedNonnegative _ := Nat.cast_nonneg _
  deviationNonnegative := seedInverseDeviationConstant_nonnegative parameters.sigma0 radius
  referenceBound := identityFamily_norm_le L parameters.sigma0 parameters.gamma ell 2
  deviationBound := actualSeedInverse_deviation_bound parameters admissible radiusNonnegative rho alpha delta parameter epsilon
    rhoSmall alphaSmall deltaSmall parameterSmall field low baseBound

def seedDerivativeProfile (sigma radius : ℝ) : EstimateProfile :=
  ⟨fun _ => 0, seedDerivativeConstant sigma radius⟩

theorem seedDerivativeFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (rho alpha delta parameter : ℝ) :
    FamilyCoherent (fun grade => seedDerivativeCoefficient admissible grade rho alpha delta parameter) := by
  intro grade other index otherIndex same cell point
  rw [seedDerivativeCoefficient_derivative, seedDerivativeCoefficient_derivative]
  rw [show derivativeOrder index = derivativeOrder otherIndex from congrArg cartesianOrder same]

theorem seedDerivativeFamily_estimate {L ell radius : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (radiusNonnegative : 0 ≤ radius) (rho alpha delta parameter epsilon : ℝ)
    (rhoSmall : |rho| ≤ 1) (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) (field : ACore parameters 3) :
    FamilyEstimate parameters field rho epsilon 4 (seedDerivativeProfile parameters.sigma0 radius)
      (fun grade => seedDerivativeCoefficient admissible grade rho alpha delta parameter)
      (zeroFamily L parameters.sigma0 parameters.gamma ell 2 2) where
  actualCoherent := seedDerivativeFamily_coherent admissible rho alpha delta parameter
  referenceCoherent := zeroFamily_coherent L parameters.sigma0 parameters.gamma ell 2 2
  fixedNonnegative _ := le_rfl
  deviationNonnegative := seedDerivativeConstant_nonnegative parameters.sigma0 radius
  referenceBound := zeroFamily_norm L parameters.sigma0 parameters.gamma ell 2 2
  deviationBound grade := by
    change ‖seedDerivativeCoefficient admissible grade rho alpha delta parameter - 0‖ ≤ _
    rw [sub_zero]
    apply (seedDerivativeCoefficient_norm_le admissible grade radiusNonnegative rhoSmall alphaSmall deltaSmall parameterSmall).trans
    apply mul_le_mul_of_nonneg_left _ (seedDerivativeConstant_nonnegative parameters.sigma0 radius grade)
    unfold physicalBudget
    linarith [Grad.NonlinearProduct.originalGradeNorm_nonnegative (4 + grade) field, abs_nonneg epsilon]

def rotatedFrameProfile (parameters : PhaseParameters) (L : ℝ) : EstimateProfile :=
  ⟨fun _ => 0, rotatedFrameConstant parameters L⟩

theorem actualRotatedFrame_estimate {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho epsilon : ℝ) (epsilonSmall : |epsilon| ≤ 1) (field : ACore parameters 3) :
    FamilyEstimate parameters field rho epsilon 5 (rotatedFrameProfile parameters L)
      (actualRotatedFrame parameters admissible epsilon field)
      (zeroFamily L parameters.sigma0 parameters.gamma ell 3 3) where
  actualCoherent := actualRotatedFrame_coherent parameters admissible epsilon field
  referenceCoherent := zeroFamily_coherent L parameters.sigma0 parameters.gamma ell 3 3
  fixedNonnegative _ := le_rfl
  deviationNonnegative := rotatedFrameConstant_nonnegative parameters admissible.1
  referenceBound := zeroFamily_norm L parameters.sigma0 parameters.gamma ell 3 3
  deviationBound grade := by
    change ‖actualRotatedFrame parameters admissible epsilon field grade - 0‖ ≤ _
    rw [sub_zero]
    exact actualRotatedFrame_bound parameters admissible rho epsilon epsilonSmall field grade

end Grad.GaugeCoefficients.Physical.Ledger
