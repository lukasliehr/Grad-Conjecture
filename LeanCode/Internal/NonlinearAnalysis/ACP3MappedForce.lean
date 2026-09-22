import ACP2ForceMatrix

noncomputable section
open scoped BigOperators

namespace Grad.ActualCurrentPrimitives
open Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollar
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger

def mappedForceFamily {output : ℕ} (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (mapping : OperatorValue 3 output) :
    CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 output :=
  composeFamily (unitDiskAdmissible parameters) (constantFamily 1 parameters.sigma0 parameters.gamma 1 mapping)
    (forceMatrixFamily parameters L epsilon field)

theorem mappedForceFamily_coherent {output : ℕ} (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (mapping : OperatorValue 3 output)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L) :
    FamilyCoherent (mappedForceFamily parameters L epsilon field mapping) :=
  (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 mapping).comp (unitDiskAdmissible parameters)
    (forceMatrixFamily_coherent parameters L rho epsilon field low)

def mappedForceConstant {output : ℕ} (parameters : PhaseParameters) (L : ℝ)
    (mapping : OperatorValue 3 output) (grade : ℕ) : ℝ :=
  gradeProductConstant grade * fixedFamilyConstant mapping grade *
    (forceMatrixProfile parameters L).deviation grade

theorem mappedForceFamily_bound {output : ℕ} (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (mapping : OperatorValue 3 output)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (grade : ℕ) :
    ‖mappedForceFamily parameters L epsilon field mapping grade‖ ≤
      mappedForceConstant parameters L mapping grade * physicalBudget parameters field rho epsilon (5 + grade) := by
  apply (coefficientComposition_norm_le (unitDiskAdmissible parameters) grade _ _).trans
  have bound := mul_le_mul
    (mul_le_mul_of_nonneg_left (constantFamily_norm_le (unitDiskAdmissible parameters) mapping grade)
      (gradeProductConstant_nonnegative grade))
    (forceMatrixFamily_bound parameters L rho epsilon field low grade)
    (norm_nonneg _) (mul_nonneg (gradeProductConstant_nonnegative grade)
      (fixedFamilyConstant_nonnegative mapping grade))
  exact bound.trans_eq (by unfold mappedForceConstant; ring)

theorem mappedForceFamily_physicalValue {output : ℕ} (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (mapping : OperatorValue 3 output)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (mappedForceFamily parameters L epsilon field mapping grade) angle point =
      mapping.comp (coefficientPhysicalValue (forceMatrixFamily parameters L epsilon field grade) angle point) := by
  rw [mappedForceFamily, composeFamily, family_physicalValue_comp (unitDiskAdmissible parameters) _ _
    (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 mapping)
    (forceMatrixFamily_coherent parameters L rho epsilon field low),
    constantFamily_physicalValue (unitDiskAdmissible parameters)]

/-- Actual full-disk force matrix, original analytic envelope and full angular/cell
moments, with exactly the state grade t+k+6. The mapping and column are fixed
finite-dimensional contractions, not new analytic premises. -/
theorem mappedForce_fourier_bound {output : ℕ} (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (mapping : OperatorValue 3 output) (column : PhysicalValue 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (tangential radial : ℕ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ∑' mode, coefficientFourierWeightedNorm parameters (mappedForceFamily parameters L epsilon field mapping)
        (mappedForceFamily_coherent parameters L rho epsilon field mapping low) column tangential radial radius mode ≤
      (coefficientFourierConstant tangential radial *
        mappedForceConstant parameters L mapping (tangential + radial + 1) * ‖column‖) *
          physicalBudget parameters field rho epsilon (tangential + radial + 6) := by
  apply (coefficient_fourier_bound parameters _
    (mappedForceFamily_coherent parameters L rho epsilon field mapping low) column
    tangential radial radius nonnegative bounded).trans
  have bound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (mappedForceFamily_bound parameters L rho epsilon field mapping low (tangential + radial + 1))
      (coefficientFourierConstant_nonnegative tangential radial)) (norm_nonneg column)
  rw [show 5 + (tangential + radial + 1) = tangential + radial + 6 by omega] at bound
  exact bound.trans_eq (by ring)

end Grad.ActualCurrentPrimitives

