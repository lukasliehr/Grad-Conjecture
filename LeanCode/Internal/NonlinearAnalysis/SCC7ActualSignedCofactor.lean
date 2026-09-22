import SCC6OriginalCofactorFamily

noncomputable section
namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger

theorem originalInverseFamily_eq_matrixInverse (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalInverseFamily parameters L epsilon field) grade angle point =
      (originalPhysicalFrameMatrix parameters L epsilon field angle point)⁻¹ := by
  have margin := originalCoefficient_low_margin parameters L rho epsilon field low
  exact (Matrix.inv_eq_right_inv
    (originalInverseFamily_matrix_identity parameters L epsilon field margin.2.2 grade angle point).1).symm

theorem originalCofactorFamily_eq_signedCofactor (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalCofactorFamily parameters L epsilon field) grade angle point =
      originalPhysicalSignedCofactor parameters L epsilon field angle point := by
  rw [originalCofactorFamily_matrix parameters L rho epsilon field low,
    originalInverseFamily_eq_matrixInverse parameters L rho epsilon field low]
  rfl

/-- The circular signed cofactor is -I, so this family realizes B_C+I,
not B_C-I. Its original full-disk norm is paid at q+4. -/
def originalCofactorDeviation (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3 :=
  fun grade => originalCofactorFamily parameters L epsilon field grade - originalCofactorReference parameters grade

theorem originalCofactorDeviation_coherent (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L) :
    FamilyCoherent (originalCofactorDeviation parameters L epsilon field) :=
  (originalCofactorFamily_estimate parameters L rho epsilon field low).actualCoherent.sub
    (originalCofactorFamily_estimate parameters L rho epsilon field low).referenceCoherent

theorem originalCofactorDeviation_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (grade : ℕ) :
    ‖originalCofactorDeviation parameters L epsilon field grade‖ ≤
      (originalCofactorProfile parameters L).deviation grade *
        physicalBudget parameters field rho epsilon (4 + grade) :=
  (originalCofactorFamily_estimate parameters L rho epsilon field low).deviationBound grade

theorem originalCofactorDeviation_matrix (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalCofactorDeviation parameters L epsilon field) grade angle point =
      originalPhysicalSignedCofactor parameters L epsilon field angle point + 1 := by
  have estimate := originalCofactorFamily_estimate parameters L rho epsilon field low
  change familyMatrix (fun grade => originalCofactorFamily parameters L epsilon field grade -
    originalCofactorReference parameters grade) grade angle point = _
  rw [familyMatrix_sub (unitDiskAdmissible parameters) _ _
    estimate.actualCoherent estimate.referenceCoherent,
    originalCofactorFamily_eq_signedCofactor parameters L rho epsilon field low,
    originalCofactorReference_matrix, sub_neg_eq_add]

end Grad.SourceCollarCoefficients
