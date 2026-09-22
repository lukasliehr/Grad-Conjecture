import ACP1OriginalRotation

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ActualCurrentPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollar
open Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger

/-- Full original-disk force matrix (R F_C)^T F_C^{-T}. Its actual reference
recipe is zero. The polar force rows are finite Laurent contractions of this
single family; no pointwise supremum over Fourier input modes is assumed. -/
def forceMatrixFamily (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3 :=
  fun grade => rotatedProductFamily (unitDiskAdmissible parameters) (1 : Matrix (Fin 3) (Fin 3) ℂ)
    (originalRotatedFamily parameters L epsilon field) (originalInverseFamily parameters L epsilon field) grade -
      rotatedProductFamily (unitDiskAdmissible parameters) (1 : Matrix (Fin 3) (Fin 3) ℂ)
        (zeroFamily 1 parameters.sigma0 parameters.gamma 1 3 3)
        (constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceFrame) grade

def forceMatrixProfile (parameters : PhaseParameters) (L : ℝ) : EstimateProfile :=
  rotatedProductProfile (1 : Matrix (Fin 3) (Fin 3) ℂ)
    (originalRotatedProfile parameters L) (originalInverseProfile parameters L)

variable (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
variable (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)

include low

theorem forceMatrixFamily_coherent : FamilyCoherent (forceMatrixFamily parameters L epsilon field) := by
  have margin := originalCoefficient_low_margin parameters L rho epsilon field low
  exact (rotatedProductFamily_coherent (unitDiskAdmissible parameters) 1 _ _
    (originalRotatedFamily_coherent parameters L epsilon field)
    (originalInverseFamily_coherent parameters L epsilon field margin.2.2)).sub
    (rotatedProductFamily_coherent (unitDiskAdmissible parameters) 1 _ _
      (zeroFamily_coherent 1 parameters.sigma0 parameters.gamma 1 3 3)
      (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 referenceFrame))

theorem forceMatrixFamily_bound (grade : ℕ) :
    ‖forceMatrixFamily parameters L epsilon field grade‖ ≤
      (forceMatrixProfile parameters L).deviation grade *
        physicalBudget parameters field rho epsilon (5 + grade) := by
  have margin := originalCoefficient_low_margin parameters L rho epsilon field low
  have lowFive : physicalBudget parameters field rho epsilon 5 ≤ 1 :=
    (physicalBudget_monotone parameters field rho epsilon (by norm_num : 5 ≤ 6)).trans
      (low.trans (min_le_left _ _))
  exact (rotatedProductFamily_estimate (unitDiskAdmissible parameters) lowFive
    (1 : Matrix (Fin 3) (Fin 3) ℂ)
    (originalRotatedFamily_estimate parameters L rho epsilon field margin.1)
    ((originalInverseFamily_estimate parameters L rho epsilon field low).offset_mono (by norm_num : 4 ≤ 5))).deviationBound grade

theorem forceMatrixFamily_matrix (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (forceMatrixFamily parameters L epsilon field) grade angle point =
      (familyMatrix (originalRotatedFamily parameters L epsilon field) grade angle point).transpose *
        (originalPhysicalFrameMatrix parameters L epsilon field angle point)⁻¹.transpose := by
  have margin := originalCoefficient_low_margin parameters L rho epsilon field low
  have invId := originalInverseFamily_matrix_identity parameters L epsilon field margin.2.2 grade angle point
  have invEq : familyMatrix (originalInverseFamily parameters L epsilon field) grade angle point =
      (originalPhysicalFrameMatrix parameters L epsilon field angle point)⁻¹ := by
    exact Matrix.inv_eq_right_inv invId.1 |>.symm
  have formula := rotatedProduct_deviation_matrix (unitDiskAdmissible parameters) (1 : Matrix (Fin 3) (Fin 3) ℂ)
    (originalRotatedFamily parameters L epsilon field) (originalInverseFamily parameters L epsilon field)
    (originalRotatedFamily_coherent parameters L epsilon field)
    (originalInverseFamily_coherent parameters L epsilon field margin.2.2) grade angle point
  change familyMatrix (fun q => rotatedProductFamily (unitDiskAdmissible parameters)
    (1 : Matrix (Fin 3) (Fin 3) ℂ) (originalRotatedFamily parameters L epsilon field)
      (originalInverseFamily parameters L epsilon field) q -
    rotatedProductFamily (unitDiskAdmissible parameters) (1 : Matrix (Fin 3) (Fin 3) ℂ)
      (zeroFamily 1 parameters.sigma0 parameters.gamma 1 3 3)
      (constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceFrame) q) grade angle point = _
  rw [Matrix.mul_one, invEq] at formula
  exact formula

end Grad.ActualCurrentPrimitives
