import GC17FixedFamily

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation

/-- H = -F_circle^{-1}(F-F_circle), so I-H = F_circle^{-1} F. -/
def frameInverseInput {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3) :
    CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3 :=
  fun grade => -coefficientComposition admissible grade
    (constantFamily L parameters.sigma0 parameters.gamma ell referenceFrame grade)
    (actualFrameFamily parameters L ell epsilon field grade)

theorem frameInverseInput_coherent {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3) :
    FamilyCoherent (frameInverseInput parameters admissible epsilon field) := by
  have coherent := (constantFamily_coherent L parameters.sigma0 parameters.gamma ell referenceFrame).comp
    admissible (actualFrameFamily_coherent parameters admissible epsilon field)
  unfold frameInverseInput
  simpa only [neg_one_smul] using coherent.smul (-1 : ℂ)

def frameInverseInputConstant (parameters : PhaseParameters) (L : ℝ) (grade : ℕ) : ℝ :=
  gradeProductConstant grade * fixedFamilyConstant referenceFrame grade * frameConstant parameters L grade

theorem frameInverseInputConstant_nonnegative (parameters : PhaseParameters) {L : ℝ}
    (positive : 0 < L) (grade : ℕ) : 0 ≤ frameInverseInputConstant parameters L grade :=
  mul_nonneg (mul_nonneg (gradeProductConstant_nonnegative grade)
    (fixedFamilyConstant_nonnegative referenceFrame grade)) (frameConstant_nonnegative parameters positive grade)

theorem frameInverseInput_bound {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho epsilon : ℝ) (epsilonSmall : |epsilon| ≤ 1) (field : ACore parameters 3) (grade : ℕ) :
    ‖frameInverseInput parameters admissible epsilon field grade‖ ≤
      frameInverseInputConstant parameters L grade * physicalBudget parameters field rho epsilon (4 + grade) := by
  change ‖-coefficientComposition admissible grade _ _‖ ≤ _
  rw [norm_neg]
  apply (coefficientComposition_norm_le admissible grade _ _).trans
  have bound := mul_le_mul
    (mul_le_mul_of_nonneg_left (constantFamily_norm_le admissible referenceFrame grade)
      (gradeProductConstant_nonnegative grade))
    (actualFrameFamily_bound parameters admissible epsilon rho epsilonSmall field grade)
    (norm_nonneg _) (mul_nonneg (gradeProductConstant_nonnegative grade)
      (fixedFamilyConstant_nonnegative referenceFrame grade))
  simpa only [frameInverseInputConstant, mul_assoc] using bound

theorem frameInverseInput_base_le {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3) :
    ‖frameInverseInput parameters admissible epsilon field 0‖ ≤
      ‖actualFrameFamily parameters L ell epsilon field 0‖ := by
  change ‖-coefficientComposition admissible 0 _ _‖ ≤ _
  rw [norm_neg]
  apply (coefficientComposition_base_norm_le admissible _ _).trans
  have fixed : ‖constantFamily L parameters.sigma0 parameters.gamma ell referenceFrame 0‖ ≤ 1 :=
    (constantFamily_base_norm_le admissible referenceFrame).trans referenceFrame_norm_le
  simpa only [one_mul] using mul_le_mul_of_nonneg_right fixed
    (norm_nonneg (actualFrameFamily parameters L ell epsilon field 0))

def normalizedFrameInverse {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3) :
    CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3 :=
  inverseFamily admissible (frameInverseInput parameters admissible epsilon field)

def actualFrameInverseDeviation {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3) :
    CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3 :=
  fun grade => coefficientComposition admissible grade
    (normalizedFrameInverse parameters admissible epsilon field grade -
      gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade 3)
    (constantFamily L parameters.sigma0 parameters.gamma ell referenceFrame grade)

def actualFrameInverse {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3) :
    CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3 :=
  fun grade => constantFamily L parameters.sigma0 parameters.gamma ell referenceFrame grade +
    actualFrameInverseDeviation parameters admissible epsilon field grade

theorem actualFrameInverseDeviation_coherent {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3)
    (baseBound : ‖frameInverseInput parameters admissible epsilon field 0‖ ≤ 1 / 4) :
    FamilyCoherent (actualFrameInverseDeviation parameters admissible epsilon field) :=
  ((inverseFamily_coherent admissible (by norm_num : 0 < 3) _
    (frameInverseInput_coherent parameters admissible epsilon field) (1 / 4) baseBound (by norm_num)).sub
      (identityFamily_coherent L parameters.sigma0 parameters.gamma ell 3)).comp
        admissible (constantFamily_coherent L parameters.sigma0 parameters.gamma ell referenceFrame)

theorem actualFrameInverse_coherent {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3)
    (baseBound : ‖frameInverseInput parameters admissible epsilon field 0‖ ≤ 1 / 4) :
    FamilyCoherent (actualFrameInverse parameters admissible epsilon field) :=
  (constantFamily_coherent L parameters.sigma0 parameters.gamma ell referenceFrame).add
    (actualFrameInverseDeviation_coherent parameters admissible epsilon field baseBound)

def frameInverseDeviationConstant (parameters : PhaseParameters) (L : ℝ) (grade : ℕ) : ℝ :=
  gradeProductConstant grade *
    inverseNormConstant (frameInverseInputConstant parameters L) 4 grade 1 (1 / 4) *
      fixedFamilyConstant referenceFrame grade

theorem frameInverseDeviationConstant_nonnegative (parameters : PhaseParameters) {L : ℝ}
    (positive : 0 < L) (grade : ℕ) : 0 ≤ frameInverseDeviationConstant parameters L grade :=
  mul_nonneg (mul_nonneg (gradeProductConstant_nonnegative grade)
    (inverseNormConstant_nonnegative _ (frameInverseInputConstant_nonnegative parameters positive)
      4 grade (by norm_num : 0 ≤ (1 : ℝ)) (by norm_num : (1 / 4 : ℝ) < 1)))
    (fixedFamilyConstant_nonnegative referenceFrame grade)

theorem actualFrameInverseDeviation_bound {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho epsilon : ℝ) (epsilonSmall : |epsilon| ≤ 1) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 4 ≤ 1)
    (baseBound : ‖frameInverseInput parameters admissible epsilon field 0‖ ≤ 1 / 4) (grade : ℕ) :
    ‖actualFrameInverseDeviation parameters admissible epsilon field grade‖ ≤
      frameInverseDeviationConstant parameters L grade * physicalBudget parameters field rho epsilon (4 + grade) := by
  have inverseBound := inverse_norm_one_high parameters admissible 4 grade field rho epsilon 1 (1 / 4)
    (by norm_num) (by norm_num) low (by norm_num : 0 < 3)
    (frameInverseInput parameters admissible epsilon field)
    (frameInverseInput_coherent parameters admissible epsilon field) (frameInverseInputConstant parameters L)
    (frameInverseInputConstant_nonnegative parameters admissible.1)
    (frameInverseInput_bound parameters admissible rho epsilon epsilonSmall field) baseBound
  change ‖coefficientComposition admissible grade _ _‖ ≤ _
  apply (coefficientComposition_norm_le admissible grade _ _).trans
  have bound := mul_le_mul
    (mul_le_mul_of_nonneg_left inverseBound (gradeProductConstant_nonnegative grade))
    (constantFamily_norm_le admissible referenceFrame grade) (norm_nonneg _)
    (mul_nonneg (gradeProductConstant_nonnegative grade)
      (mul_nonneg (inverseNormConstant_nonnegative _
        (frameInverseInputConstant_nonnegative parameters admissible.1) 4 grade
        (by norm_num : 0 ≤ (1 : ℝ)) (by norm_num : (1 / 4 : ℝ) < 1))
        (physicalBudget_nonnegative parameters field rho epsilon (4 + grade))))
  calc
    _ ≤ _ := bound
    _ = _ := by unfold frameInverseDeviationConstant; ring

end Grad.GaugeCoefficients.Physical.Ledger
