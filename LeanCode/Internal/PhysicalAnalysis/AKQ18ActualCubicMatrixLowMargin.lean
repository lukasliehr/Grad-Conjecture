import AKQ17CubicMatrixCoefficientFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.Ledger

def originalCubicMatrixFamily (parameters : PhaseParameters) (length epsilon : ℝ) (field : ACore parameters 3) :
    CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 2 2 :=
  cubicMatrixFamily (unitDiskAdmissible parameters) (originalAxisGramFamily parameters length epsilon field)

def originalCubicMatrixReference (parameters : PhaseParameters) : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 2 2 :=
  cubicMatrixFamily (unitDiskAdmissible parameters) (originalAxisGramReference parameters)

def originalCubicMatrixProfile (parameters : PhaseParameters) (length : ℝ) : EstimateProfile :=
  cubicMatrixProfile (originalAxisGramProfile parameters length)

theorem originalCubicMatrixFamily_estimate (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length) :
    FamilyEstimate parameters field rho epsilon 4 (originalCubicMatrixProfile parameters length)
      (originalCubicMatrixFamily parameters length epsilon field) (originalCubicMatrixReference parameters) :=
  cubicMatrixFamily_estimate (originalCoefficient_low_margin parameters length rho epsilon field low).2.1
    (originalAxisGramFamily_estimate parameters length rho epsilon field low)

/-- H=−D_I^-1(D_K0−D_I), so I−H=D_I^-1 D_K0 at every actual circle value. -/
def originalCubicInverseInput (parameters : PhaseParameters) (length epsilon : ℝ) (field : ACore parameters 3) :
    CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 2 2 :=
  composeFamily (unitDiskAdmissible parameters)
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 (-referenceCubicInverse))
    (fun grade => originalCubicMatrixFamily parameters length epsilon field grade - originalCubicMatrixReference parameters grade)

def originalCubicInputConstant (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) : ℝ :=
  |gradeProductConstant grade * fixedFamilyConstant (-referenceCubicInverse) grade *
    (originalCubicMatrixProfile parameters length).deviation grade|

theorem originalCubicInverseInput_coherent (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length) :
    FamilyCoherent (originalCubicInverseInput parameters length epsilon field) :=
  (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 (-referenceCubicInverse)).comp
    (unitDiskAdmissible parameters)
    ((originalCubicMatrixFamily_estimate parameters length rho epsilon field low).actualCoherent.sub
      (originalCubicMatrixFamily_estimate parameters length rho epsilon field low).referenceCoherent)

theorem originalCubicInverseInput_bound (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length) (grade : ℕ) :
    ‖originalCubicInverseInput parameters length epsilon field grade‖ ≤
      originalCubicInputConstant parameters length grade * physicalBudget parameters field rho epsilon (4 + grade) := by
  have estimate := originalCubicMatrixFamily_estimate parameters length rho epsilon field low
  apply (coefficientComposition_norm_le (unitDiskAdmissible parameters) grade _ _).trans
  have product := mul_le_mul
    (mul_le_mul_of_nonneg_left (constantFamily_norm_le (unitDiskAdmissible parameters) (-referenceCubicInverse) grade)
      (gradeProductConstant_nonnegative grade))
    (estimate.deviationBound grade) (norm_nonneg _)
    (mul_nonneg (gradeProductConstant_nonnegative grade) (fixedFamilyConstant_nonnegative (-referenceCubicInverse) grade))
  apply product.trans
  calc
    _ = (gradeProductConstant grade * fixedFamilyConstant (-referenceCubicInverse) grade *
        (originalCubicMatrixProfile parameters length).deviation grade) *
      physicalBudget parameters field rho epsilon (4 + grade) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_abs_self _) (physicalBudget_nonnegative _ _ _ _ _)

/-- One genuine low radius, chosen before any higher grade. The original
physical budget is retained; no high-grade smallness is introduced. -/
def originalCubicLowRadius (parameters : PhaseParameters) (length : ℝ) : ℝ :=
  min (originalCoefficientLowRadius parameters length) (4 * (originalCubicInputConstant parameters length 0 + 1))⁻¹

theorem originalCubicLowRadius_positive (parameters : PhaseParameters) (length : ℝ) :
    0 < originalCubicLowRadius parameters length := by
  apply lt_min (originalCoefficientLowRadius_positive parameters length)
  have nonnegative : 0 ≤ originalCubicInputConstant parameters length 0 := abs_nonneg _
  positivity

theorem originalCubic_low_margin (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) :
    physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length ∧
      physicalBudget parameters field rho epsilon 4 ≤ 1 ∧
      ‖originalCubicInverseInput parameters length epsilon field 0‖ ≤ 1 / 4 := by
  have oldLow := low.trans (min_le_left _ _)
  have monotone := physicalBudget_monotone parameters field rho epsilon (by norm_num : 4 ≤ 6)
  refine ⟨oldLow,(originalCoefficient_low_margin parameters length rho epsilon field oldLow).2.1,?_⟩
  apply (originalCubicInverseInput_bound parameters length rho epsilon field oldLow 0).trans
  have baseLow : physicalBudget parameters field rho epsilon 4 ≤
      (4 * (originalCubicInputConstant parameters length 0 + 1))⁻¹ := monotone.trans (low.trans (min_le_right _ _))
  have nonnegative : 0 ≤ originalCubicInputConstant parameters length 0 := abs_nonneg _
  apply (mul_le_mul_of_nonneg_left baseLow nonnegative).trans
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : 0 < 4 * (originalCubicInputConstant parameters length 0 + 1))).mpr
  linarith

end Grad.FinitePhysicalJetLift
