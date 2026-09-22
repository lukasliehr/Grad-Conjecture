import SCC1GlobalFrame

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger

/-- Normalized perturbation of the original full-disk frame. This is not
the cap frame at a smaller physical point. -/
def originalInverseInput (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3 :=
  fun grade => -coefficientComposition (unitDiskAdmissible parameters) grade
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceFrame grade)
    (originalFrameFamily parameters L epsilon field grade)

theorem originalInverseInput_coherent (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) : FamilyCoherent (originalInverseInput parameters L epsilon field) := by
  have coherent := (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 referenceFrame).comp
    (unitDiskAdmissible parameters) (originalFrameFamily_coherent parameters L epsilon field)
  unfold originalInverseInput
  simpa only [neg_one_smul] using coherent.smul (-1 : ℂ)

def originalInverseInputConstant (parameters : PhaseParameters) (L : ℝ) (grade : ℕ) : ℝ :=
  gradeProductConstant grade * fixedFamilyConstant referenceFrame grade *
    originalFrameConstant parameters L grade

theorem originalInverseInputConstant_nonnegative (parameters : PhaseParameters) (L : ℝ) (grade : ℕ) :
    0 ≤ originalInverseInputConstant parameters L grade :=
  mul_nonneg (mul_nonneg (gradeProductConstant_nonnegative grade)
    (fixedFamilyConstant_nonnegative referenceFrame grade))
    (originalFrameConstant_nonnegative parameters L grade)

theorem originalInverseInput_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (epsilonSmall : |epsilon| ≤ 1) (grade : ℕ) :
    ‖originalInverseInput parameters L epsilon field grade‖ ≤
      originalInverseInputConstant parameters L grade * physicalBudget parameters field rho epsilon (4 + grade) := by
  change ‖-coefficientComposition (unitDiskAdmissible parameters) grade _ _‖ ≤ _
  rw [norm_neg]
  apply (coefficientComposition_norm_le (unitDiskAdmissible parameters) grade _ _).trans
  have bound := mul_le_mul
    (mul_le_mul_of_nonneg_left
      (constantFamily_norm_le (unitDiskAdmissible parameters) referenceFrame grade)
      (gradeProductConstant_nonnegative grade))
    (originalFrameFamily_bound parameters L rho epsilon field epsilonSmall grade)
    (norm_nonneg _) (mul_nonneg (gradeProductConstant_nonnegative grade)
      (fixedFamilyConstant_nonnegative referenceFrame grade))
  simpa only [originalInverseInputConstant, mul_assoc] using bound

/-- One B6 radius, chosen before every higher grade. -/
def originalCoefficientLowRadius (parameters : PhaseParameters) (L : ℝ) : ℝ :=
  min 1 (4 * (originalInverseInputConstant parameters L 0 + 1))⁻¹

theorem originalCoefficientLowRadius_positive (parameters : PhaseParameters) (L : ℝ) :
    0 < originalCoefficientLowRadius parameters L := by
  have nonnegative := originalInverseInputConstant_nonnegative parameters L 0
  unfold originalCoefficientLowRadius
  exact lt_min (by norm_num) (by positivity)

theorem originalCoefficient_low_margin (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L) :
    |epsilon| ≤ 1 ∧ physicalBudget parameters field rho epsilon 4 ≤ 1 ∧
      ‖originalInverseInput parameters L epsilon field 0‖ ≤ 1 / 4 := by
  have lowSix : physicalBudget parameters field rho epsilon 6 ≤ 1 := low.trans (min_le_left _ _)
  have epsilonSmall : |epsilon| ≤ 1 := by
    unfold physicalBudget at lowSix
    linarith [Grad.NonlinearProduct.originalGradeNorm_nonnegative 6 field, abs_nonneg rho]
  have monotone := physicalBudget_monotone parameters field rho epsilon (by norm_num : 4 ≤ 6)
  refine ⟨epsilonSmall, monotone.trans lowSix, ?_⟩
  have baseLow : physicalBudget parameters field rho epsilon 4 ≤
      (4 * (originalInverseInputConstant parameters L 0 + 1))⁻¹ :=
    monotone.trans (low.trans (min_le_right _ _))
  have nonnegative := originalInverseInputConstant_nonnegative parameters L 0
  apply (originalInverseInput_bound parameters L rho epsilon field epsilonSmall 0).trans
  apply (mul_le_mul_of_nonneg_left baseLow nonnegative).trans
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : 0 < 4 * (originalInverseInputConstant parameters L 0 + 1))).mpr
  linarith

end Grad.SourceCollarCoefficients
