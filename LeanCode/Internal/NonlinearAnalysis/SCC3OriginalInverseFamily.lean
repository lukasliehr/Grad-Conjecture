import SCC2OriginalInverseInput

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation Grad.GaugeCoefficients.Physical.Ledger

def originalInverseDeviation (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3 :=
  fun grade => coefficientComposition (unitDiskAdmissible parameters) grade
    (inverseFamily (unitDiskAdmissible parameters) (originalInverseInput parameters L epsilon field) grade -
      gradedIdentityCoefficient 1 parameters.sigma0 parameters.gamma 1 grade 3)
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceFrame grade)

def originalInverseFamily (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3 :=
  fun grade => constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceFrame grade +
    originalInverseDeviation parameters L epsilon field grade

theorem originalInverseDeviation_coherent (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3)
    (baseBound : ‖originalInverseInput parameters L epsilon field 0‖ ≤ 1 / 4) :
    FamilyCoherent (originalInverseDeviation parameters L epsilon field) :=
  ((inverseFamily_coherent (unitDiskAdmissible parameters) (by norm_num : 0 < 3) _
    (originalInverseInput_coherent parameters L epsilon field) (1 / 4) baseBound (by norm_num)).sub
      (identityFamily_coherent 1 parameters.sigma0 parameters.gamma 1 3)).comp
        (unitDiskAdmissible parameters)
        (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 referenceFrame)

theorem originalInverseFamily_coherent (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3)
    (baseBound : ‖originalInverseInput parameters L epsilon field 0‖ ≤ 1 / 4) :
    FamilyCoherent (originalInverseFamily parameters L epsilon field) :=
  (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 referenceFrame).add
    (originalInverseDeviation_coherent parameters L epsilon field baseBound)

def originalInverseConstant (parameters : PhaseParameters) (L : ℝ) (grade : ℕ) : ℝ :=
  gradeProductConstant grade *
    inverseNormConstant (originalInverseInputConstant parameters L) 4 grade 1 (1 / 4) *
      fixedFamilyConstant referenceFrame grade

theorem originalInverseConstant_nonnegative (parameters : PhaseParameters) (L : ℝ) (grade : ℕ) :
    0 ≤ originalInverseConstant parameters L grade :=
  mul_nonneg (mul_nonneg (gradeProductConstant_nonnegative grade)
    (inverseNormConstant_nonnegative _ (originalInverseInputConstant_nonnegative parameters L)
      4 grade (by norm_num : 0 ≤ (1 : ℝ)) (by norm_num : (1 / 4 : ℝ) < 1)))
    (fixedFamilyConstant_nonnegative referenceFrame grade)

/-- The existing ordered-word inverse estimate is instantiated on the
actual original-disk perturbation; only one high B_(q+4) occurs. -/
theorem originalInverseDeviation_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (epsilonSmall : |epsilon| ≤ 1)
    (low : physicalBudget parameters field rho epsilon 4 ≤ 1)
    (baseBound : ‖originalInverseInput parameters L epsilon field 0‖ ≤ 1 / 4) (grade : ℕ) :
    ‖originalInverseDeviation parameters L epsilon field grade‖ ≤
      originalInverseConstant parameters L grade * physicalBudget parameters field rho epsilon (4 + grade) := by
  have inverseBound := inverse_norm_one_high parameters (unitDiskAdmissible parameters)
    4 grade field rho epsilon 1 (1 / 4) (by norm_num) (by norm_num) low (by norm_num : 0 < 3)
    (originalInverseInput parameters L epsilon field)
    (originalInverseInput_coherent parameters L epsilon field) (originalInverseInputConstant parameters L)
    (originalInverseInputConstant_nonnegative parameters L)
    (originalInverseInput_bound parameters L rho epsilon field epsilonSmall) baseBound
  apply (coefficientComposition_norm_le (unitDiskAdmissible parameters) grade _ _).trans
  have bound := mul_le_mul
    (mul_le_mul_of_nonneg_left inverseBound (gradeProductConstant_nonnegative grade))
    (constantFamily_norm_le (unitDiskAdmissible parameters) referenceFrame grade)
    (norm_nonneg _) (mul_nonneg (gradeProductConstant_nonnegative grade)
      (mul_nonneg (inverseNormConstant_nonnegative _
        (originalInverseInputConstant_nonnegative parameters L) 4 grade
        (by norm_num : 0 ≤ (1 : ℝ)) (by norm_num : (1 / 4 : ℝ) < 1))
        (physicalBudget_nonnegative parameters field rho epsilon (4 + grade))))
  calc
    _ ≤ _ := bound
    _ = _ := by unfold originalInverseConstant; ring

def originalInverseProfile (parameters : PhaseParameters) (L : ℝ) : EstimateProfile :=
  ⟨fixedFamilyConstant referenceFrame, originalInverseConstant parameters L⟩

theorem originalInverseFamily_estimate (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L) :
    FamilyEstimate parameters field rho epsilon 4 (originalInverseProfile parameters L)
      (originalInverseFamily parameters L epsilon field)
      (constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceFrame) := by
  have margin := originalCoefficient_low_margin parameters L rho epsilon field low
  refine ⟨originalInverseFamily_coherent parameters L epsilon field margin.2.2,
    constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 referenceFrame,
    fixedFamilyConstant_nonnegative referenceFrame, originalInverseConstant_nonnegative parameters L,
    constantFamily_norm_le (unitDiskAdmissible parameters) referenceFrame, ?_⟩
  intro grade
  change ‖(_ + originalInverseDeviation parameters L epsilon field grade) - _‖ ≤ _
  rw [add_sub_cancel_left]
  exact originalInverseDeviation_bound parameters L rho epsilon field margin.1 margin.2.1 margin.2.2 grade

end Grad.SourceCollarCoefficients
