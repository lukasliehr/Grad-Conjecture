import SC8PublicBoundary
import GC17Consumer

noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger

/-- Algebra coordinates are the original unit disk. The physical length is
retained separately in the literal third column, even when L < 1. -/
theorem unitDiskAdmissible (parameters : PhaseParameters) :
    Admissible 1 parameters.sigma0 parameters.gamma 1 :=
  ⟨by norm_num, parameters.gamma_pos, parameters.gamma_lt_min, by norm_num, by norm_num⟩

def physicalColumnScale (L : ℝ) : OperatorValue 3 3 :=
  matrixOperator (Matrix.diagonal ![1, 1, (L : ℂ)⁻¹])

theorem physicalColumnScale_apply (L : ℝ) (value : ComplexEuclidean 3) :
    physicalColumnScale L value = WithLp.toLp 2 ![value 0, value 1, (L : ℂ)⁻¹ * value 2] := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [physicalColumnScale, matrixOperator, Fintype.sum_prod_type,
    Fin.sum_univ_three, matrixUnit, columnEmbedding_apply, operatorBasis]

/-- Full-cell coefficient of the actual, unscaled original frame deviation.
Only its third column is multiplied by the fixed physical factor L⁻¹. -/
def originalFrameFamily (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3 :=
  composeFamily (unitDiskAdmissible parameters)
    (actualFrameFamily parameters 1 1 epsilon field)
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 (physicalColumnScale L))

theorem originalFrameFamily_coherent (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) : FamilyCoherent (originalFrameFamily parameters L epsilon field) :=
  (actualFrameFamily_coherent parameters (unitDiskAdmissible parameters) epsilon field).comp
    (unitDiskAdmissible parameters)
    (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 (physicalColumnScale L))

def originalFrameConstant (parameters : PhaseParameters) (L : ℝ) (grade : ℕ) : ℝ :=
  gradeProductConstant grade * frameConstant parameters 1 grade *
    fixedFamilyConstant (physicalColumnScale L) grade

theorem originalFrameConstant_nonnegative (parameters : PhaseParameters) (L : ℝ) (grade : ℕ) :
    0 ≤ originalFrameConstant parameters L grade :=
  mul_nonneg (mul_nonneg (gradeProductConstant_nonnegative grade)
    (frameConstant_nonnegative parameters (by norm_num) grade))
    (fixedFamilyConstant_nonnegative (physicalColumnScale L) grade)

theorem originalFrameFamily_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (epsilonSmall : |epsilon| ≤ 1) (grade : ℕ) :
    ‖originalFrameFamily parameters L epsilon field grade‖ ≤
      originalFrameConstant parameters L grade * physicalBudget parameters field rho epsilon (4 + grade) := by
  apply (coefficientComposition_norm_le (unitDiskAdmissible parameters) grade _ _).trans
  have bound := mul_le_mul
    (mul_le_mul_of_nonneg_left
      (actualFrameFamily_bound parameters (unitDiskAdmissible parameters) epsilon rho epsilonSmall field grade)
      (gradeProductConstant_nonnegative grade))
    (constantFamily_norm_le (unitDiskAdmissible parameters) (physicalColumnScale L) grade)
    (norm_nonneg _) (mul_nonneg (gradeProductConstant_nonnegative grade)
      (mul_nonneg (frameConstant_nonnegative parameters (by norm_num) grade)
        (physicalBudget_nonnegative parameters field rho epsilon (4 + grade))))
  calc
    _ ≤ _ := bound
    _ = _ := by unfold originalFrameConstant; ring

theorem frameDeviationCell_columnScale (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (cell : ℤ) (point : ClosedDisk) :
    (frameDeviationCell parameters 1 epsilon (GradeCore.ofCoreLinear (grade := 4) field) cell point).comp
      (physicalColumnScale L) =
      frameDeviationCell parameters L epsilon (GradeCore.ofCoreLinear (grade := 4) field) cell point := by
  apply ContinuousLinearMap.ext
  intro value
  rw [ContinuousLinearMap.comp_apply, physicalColumnScale_apply]
  apply PiLp.ext
  intro coordinate
  simp only [frameDeviationCell, add_apply, columnEmbedding_apply, PiLp.add_apply,
    PiLp.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, smul_eq_mul, Complex.ofReal_one, inv_one, one_smul]
  dsimp
  ring

end Grad.SourceCollarCoefficients
