import AKQ19ActualCubicMatrixCircleIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation Grad.GaugeCoefficients.Physical.Ledger

def originalCubicInverseDeviation (parameters : PhaseParameters) (length epsilon : ℝ) (field : ACore parameters 3) :
    CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 2 2 :=
  composeFamily (unitDiskAdmissible parameters)
    (fun grade => inverseFamily (unitDiskAdmissible parameters) (originalCubicInverseInput parameters length epsilon field) grade -
      gradedIdentityCoefficient 1 parameters.sigma0 parameters.gamma 1 grade 2)
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceCubicInverse)

/-- One accepted ordered Neumann series at the original width, followed
by the verified fixed inverse D_I^-1. Every higher grade is this same inverse. -/
def originalCubicInverseFamily (parameters : PhaseParameters) (length epsilon : ℝ) (field : ACore parameters 3) :
    CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 2 2 :=
  fun grade => constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceCubicInverse grade +
    originalCubicInverseDeviation parameters length epsilon field grade

theorem originalCubicNeumann_coherent (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) :
    FamilyCoherent (inverseFamily (unitDiskAdmissible parameters) (originalCubicInverseInput parameters length epsilon field)) :=
  inverseFamily_coherent (unitDiskAdmissible parameters) (by norm_num : 0 < 2) _
    (originalCubicInverseInput_coherent parameters length rho epsilon field (originalCubic_low_margin parameters length rho epsilon field low).1)
    (1/4) (originalCubic_low_margin parameters length rho epsilon field low).2.2 (by norm_num)

theorem originalCubicInverseDeviation_coherent (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) :
    FamilyCoherent (originalCubicInverseDeviation parameters length epsilon field) :=
  ((originalCubicNeumann_coherent parameters length rho epsilon field low).sub
    (identityFamily_coherent 1 parameters.sigma0 parameters.gamma 1 2)).comp (unitDiskAdmissible parameters)
    (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 referenceCubicInverse)

theorem originalCubicInverseFamily_coherent (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) :
    FamilyCoherent (originalCubicInverseFamily parameters length epsilon field) :=
  (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 referenceCubicInverse).add
    (originalCubicInverseDeviation_coherent parameters length rho epsilon field low)

def originalCubicInverseConstant (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) : ℝ :=
  gradeProductConstant grade * inverseNormConstant (originalCubicInputConstant parameters length) 4 grade 1 (1/4) *
    fixedFamilyConstant referenceCubicInverse grade

theorem originalCubicInverseConstant_nonnegative (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) :
    0 ≤ originalCubicInverseConstant parameters length grade :=
  mul_nonneg (mul_nonneg (gradeProductConstant_nonnegative grade)
    (inverseNormConstant_nonnegative _ (fun _ => abs_nonneg _) 4 grade (by norm_num : 0 ≤ (1 : ℝ)) (by norm_num : (1/4 : ℝ) < 1)))
    (fixedFamilyConstant_nonnegative referenceCubicInverse grade)

/-- The actual all-grade inverse deviation has one high original B_(q+4)
factor. The low radius and the ordered base inverse are independent of q. -/
theorem originalCubicInverseFamily_one_high (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length) (grade : ℕ) :
    ‖originalCubicInverseFamily parameters length epsilon field grade -
      constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceCubicInverse grade‖ ≤
      originalCubicInverseConstant parameters length grade * physicalBudget parameters field rho epsilon (4 + grade) := by
  have margin := originalCubic_low_margin parameters length rho epsilon field low
  have bound := inverse_norm_one_high parameters (unitDiskAdmissible parameters) 4 grade field rho epsilon 1 (1/4)
    (by norm_num) (by norm_num) margin.2.1 (by norm_num : 0 < 2)
    (originalCubicInverseInput parameters length epsilon field)
    (originalCubicInverseInput_coherent parameters length rho epsilon field margin.1)
    (originalCubicInputConstant parameters length) (fun _ => abs_nonneg _)
    (originalCubicInverseInput_bound parameters length rho epsilon field margin.1) margin.2.2
  change ‖(_ + originalCubicInverseDeviation parameters length epsilon field grade) - _‖ ≤ _
  rw [add_sub_cancel_left]
  apply (coefficientComposition_norm_le (unitDiskAdmissible parameters) grade _ _).trans
  have product := mul_le_mul
    (mul_le_mul_of_nonneg_left bound (gradeProductConstant_nonnegative grade))
    (constantFamily_norm_le (unitDiskAdmissible parameters) referenceCubicInverse grade) (norm_nonneg _)
    (mul_nonneg (gradeProductConstant_nonnegative grade)
      (mul_nonneg (inverseNormConstant_nonnegative _ (fun _ => abs_nonneg _) 4 grade (by norm_num : 0 ≤ (1 : ℝ)) (by norm_num : (1/4 : ℝ) < 1))
        (physicalBudget_nonnegative parameters field rho epsilon (4 + grade))))
  exact product.trans_eq (by unfold originalCubicInverseConstant; ring)

theorem originalCubicInverseFamily_physicalValue (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (originalCubicInverseFamily parameters length epsilon field grade) angle point =
      (fourierEvaluation (analyticCapCoefficientNeumannInverse (unitDiskAdmissible parameters)
        (originalCubicInverseInput parameters length epsilon field 0)) angle point).comp referenceCubicInverse := by
  have margin := originalCubic_low_margin parameters length rho epsilon field low
  have fixed := constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 referenceCubicInverse
  have inverse := originalCubicNeumann_coherent parameters length rho epsilon field low
  have identity := identityFamily_coherent 1 parameters.sigma0 parameters.gamma 1 2
  rw [originalCubicInverseFamily,family_physicalValue_add (unitDiskAdmissible parameters) _ _ fixed
    (originalCubicInverseDeviation_coherent parameters length rho epsilon field low),
    originalCubicInverseDeviation,composeFamily,family_physicalValue_comp (unitDiskAdmissible parameters) _ _ (inverse.sub identity) fixed,
    family_physicalValue_sub (unitDiskAdmissible parameters) _ _ inverse identity,
    constantFamily_physicalValue (unitDiskAdmissible parameters),identityFamily_physicalValue,
    inverseFamily_physicalValue (unitDiskAdmissible parameters) (by norm_num : 0 < 2) _
      (originalCubicInverseInput_coherent parameters length rho epsilon field margin.1) (1/4) margin.2.2 (by norm_num)]
  change referenceCubicInverse + (_ - 1) * referenceCubicInverse = _ * referenceCubicInverse
  rw [sub_mul,one_mul]
  abel

end Grad.FinitePhysicalJetLift
