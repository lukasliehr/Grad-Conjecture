import AKX11ActualSourceGlobalPhysicalFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter
open scoped Topology BigOperators
namespace Grad.ActualPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollar
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

/-- The already constructed original frame inverse, transposed. -/
def originalInverseTransposeFamily (parameters : PhaseParameters) (length epsilon : ℝ) (field : ACore parameters 3) :=
  transposeFamily (unitDiskAdmissible parameters) (originalInverseFamily parameters length epsilon field)

def originalInverseTransposeProfile (parameters : PhaseParameters) (length : ℝ) : EstimateProfile :=
  transposeProfile 4 3 3 (originalInverseProfile parameters length)

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)

include small

theorem originalInverseTransposeFamily_estimate :
    FamilyEstimate parameters field rho epsilon 4 (originalInverseTransposeProfile parameters length)
      (originalInverseTransposeFamily parameters length epsilon field)
      (transposeFamily (unitDiskAdmissible parameters)
        (constantFamily 1 parameters.sigma0 parameters.gamma 1 Grad.GaugeCoefficients.Physical.Frame.referenceFrame)) :=
  transposeFamily_estimate (unitDiskAdmissible parameters)
    (originalCoefficient_low_margin parameters length rho epsilon field small).2.1
    (originalInverseFamily_estimate parameters length rho epsilon field small)

theorem originalInverseTransposeFamily_coherent :
    FamilyCoherent (originalInverseTransposeFamily parameters length epsilon field) :=
  (originalInverseTransposeFamily_estimate parameters length rho epsilon field small).actualCoherent

theorem originalInverseTransposeFamily_matrix (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalInverseTransposeFamily parameters length epsilon field) grade angle point =
      (familyMatrix (originalInverseFamily parameters length epsilon field) grade angle point).transpose :=
  familyMatrix_transpose (unitDiskAdmissible parameters) _
    (originalInverseFamily_coherent parameters length epsilon field
      (originalCoefficient_low_margin parameters length rho epsilon field small).2.2) grade angle point

/-- Exact physical F^T U = w recovery at every point, including the axis. -/
theorem originalInverseTransposeFamily_two_sided (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    let frame := originalPhysicalFrameMatrix parameters length epsilon field angle point
    let inverseTranspose := familyMatrix (originalInverseTransposeFamily parameters length epsilon field) grade angle point
    frame.transpose * inverseTranspose = 1 ∧ inverseTranspose * frame.transpose = 1 := by
  dsimp only
  rw [originalInverseTransposeFamily_matrix parameters length rho epsilon field small]
  have actual := originalInverseFamily_matrix_identity parameters length epsilon field
    (originalCoefficient_low_margin parameters length rho epsilon field small).2.2 grade angle point
  constructor
  · simpa only [Matrix.transpose_mul,Matrix.transpose_one] using congrArg Matrix.transpose actual.2
  · simpa only [Matrix.transpose_mul,Matrix.transpose_one] using congrArg Matrix.transpose actual.1

end Grad.ActualPhysicalField
