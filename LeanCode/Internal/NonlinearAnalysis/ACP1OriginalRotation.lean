import SCC15KappaLaurent
import GC17PrimitiveEstimates

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ActualCurrentPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollar
open Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger

/-- Actual angular derivative of the original Cartesian frame. The fixed
physical third-column factor retains arbitrary L, including L<1. -/
def originalRotatedFamily (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3 :=
  composeFamily (unitDiskAdmissible parameters)
    (actualRotatedFrame parameters (unitDiskAdmissible parameters) epsilon field)
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 (physicalColumnScale L))

theorem originalRotatedFamily_coherent (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) : FamilyCoherent (originalRotatedFamily parameters L epsilon field) :=
  (actualRotatedFrame_coherent parameters (unitDiskAdmissible parameters) epsilon field).comp
    (unitDiskAdmissible parameters)
    (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 (physicalColumnScale L))

def originalRotatedConstant (parameters : PhaseParameters) (L : ℝ) (grade : ℕ) : ℝ :=
  gradeProductConstant grade * rotatedFrameConstant parameters 1 grade *
    fixedFamilyConstant (physicalColumnScale L) grade

theorem originalRotatedConstant_nonnegative (parameters : PhaseParameters) (L : ℝ) (grade : ℕ) :
    0 ≤ originalRotatedConstant parameters L grade :=
  mul_nonneg (mul_nonneg (gradeProductConstant_nonnegative grade)
    (rotatedFrameConstant_nonnegative parameters (by norm_num) grade))
    (fixedFamilyConstant_nonnegative (physicalColumnScale L) grade)

theorem originalRotatedFamily_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (epsilonSmall : |epsilon| ≤ 1) (grade : ℕ) :
    ‖originalRotatedFamily parameters L epsilon field grade‖ ≤
      originalRotatedConstant parameters L grade * physicalBudget parameters field rho epsilon (5 + grade) := by
  apply (coefficientComposition_norm_le (unitDiskAdmissible parameters) grade _ _).trans
  have bound := mul_le_mul
    (mul_le_mul_of_nonneg_left
      (actualRotatedFrame_bound parameters (unitDiskAdmissible parameters) rho epsilon epsilonSmall field grade)
      (gradeProductConstant_nonnegative grade))
    (constantFamily_norm_le (unitDiskAdmissible parameters) (physicalColumnScale L) grade)
    (norm_nonneg _) (mul_nonneg (gradeProductConstant_nonnegative grade)
      (mul_nonneg (rotatedFrameConstant_nonnegative parameters (by norm_num) grade)
        (physicalBudget_nonnegative parameters field rho epsilon (5 + grade))))
  exact bound.trans_eq (by unfold originalRotatedConstant; ring)

def originalRotatedProfile (parameters : PhaseParameters) (L : ℝ) : EstimateProfile :=
  ⟨fun _ => 0, originalRotatedConstant parameters L⟩

theorem originalRotatedFamily_estimate (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (epsilonSmall : |epsilon| ≤ 1) :
    FamilyEstimate parameters field rho epsilon 5 (originalRotatedProfile parameters L)
      (originalRotatedFamily parameters L epsilon field)
      (zeroFamily 1 parameters.sigma0 parameters.gamma 1 3 3) where
  actualCoherent := originalRotatedFamily_coherent parameters L epsilon field
  referenceCoherent := zeroFamily_coherent 1 parameters.sigma0 parameters.gamma 1 3 3
  fixedNonnegative _ := le_rfl
  deviationNonnegative := originalRotatedConstant_nonnegative parameters L
  referenceBound := zeroFamily_norm 1 parameters.sigma0 parameters.gamma 1 3 3
  deviationBound grade := by
    change ‖originalRotatedFamily parameters L epsilon field grade - 0‖ ≤ _
    rw [sub_zero]
    exact originalRotatedFamily_bound parameters L rho epsilon field epsilonSmall grade

theorem originalRotatedFamily_matrix (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalRotatedFamily parameters L epsilon field) grade angle point =
      rotatedPhysicalFrameMatrix parameters 1 1 epsilon field angle point *
        Matrix.diagonal ![1, 1, (L : ℂ)⁻¹] := by
  rw [originalRotatedFamily, familyMatrix_comp (unitDiskAdmissible parameters) _ _
    (actualRotatedFrame_coherent parameters (unitDiskAdmissible parameters) epsilon field)
    (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 (physicalColumnScale L)),
    physicalColumnScale, familyMatrix_constant (unitDiskAdmissible parameters)]
  change operatorMatrix (coefficientPhysicalValue _ angle point) * _ = _
  rw [actualRotatedFrame_physicalValue parameters (unitDiskAdmissible parameters)]

end Grad.ActualCurrentPrimitives
