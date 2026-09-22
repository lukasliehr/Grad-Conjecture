import AKAQ6WeightedDerivativeTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators ContDiff
namespace Grad.OriginalFlatAxisDecay
open Grad.FourierGrade Grad.CartesianState Grad.ClosedJets Grad.COR12Extension
open Grad.COR13Completion Grad.SourceCollarDivision Grad.Constraints
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.BoundaryLift

theorem origin_val : (ambientClosedDisk 0).val = 0 :=
  ambientClosedDisk_val_of_mem (by simp [closedUnitDisk])

def weightedTaylorAt {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ) (point : ClosedDisk) :
    AGrade parameters dimension 4 →L[ℂ] ComplexEuclidean dimension :=
  weightedValueAt parameters cell point - weightedValueAt parameters cell (ambientClosedDisk 0) -
    (point.val 0 : ℂ) • weightedDerivativeAt parameters cell 0 (ambientClosedDisk 0) -
    (point.val 1 : ℂ) • weightedDerivativeAt parameters cell 1 (ambientClosedDisk 0)

def weightedRotationRemainderAt {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ) (point : ClosedDisk) :
    AGrade parameters dimension 4 →L[ℂ] ComplexEuclidean dimension :=
  (point.val 0 : ℂ) • (weightedDerivativeAt parameters cell 1 point - weightedDerivativeAt parameters cell 1 (ambientClosedDisk 0)) -
    (point.val 1 : ℂ) • (weightedDerivativeAt parameters cell 0 point - weightedDerivativeAt parameters cell 0 (ambientClosedDisk 0))

theorem imaginaryWaveLinear_decompose (mode : SpatialMode) (point : SpatialPlane) :
    imaginaryWaveLinear mode point =
      (point 0 : ℂ) * imaginaryWaveLinear mode (spatialBasis 0) +
      (point 1 : ℂ) * imaginaryWaveLinear mode (spatialBasis 1) := by
  conv_lhs => arg 2; rw [spatialPlane_decompose point]
  rw [map_add,map_smul,map_smul]
  rfl

theorem imaginaryWaveLinear_rotation (mode : SpatialMode) (point : SpatialPlane) :
    (point 0 : ℂ) * imaginaryWaveLinear mode (spatialBasis 1) -
      (point 1 : ℂ) * imaginaryWaveLinear mode (spatialBasis 0) =
      Complex.I * (rotationWave mode point : ℂ) := by
  simp [imaginaryWaveLinear_apply,waveAngle,rotationWave,spatialBasis]
  ring

theorem weightedValueAt_single {dimension : ℕ} (parameters : PhaseParameters)
    (mode : SpatialMode) (source cell : ℤ) (value : ComplexEuclidean dimension) (point : ClosedDisk) :
    weightedValueAt parameters cell point
      (completedRetraction parameters (coefficientSingle 4 (fibreMode (source,mode)) value)) =
      if source = cell then Complex.exp (imaginaryWaveLinear mode point.val) • value else 0 :=
  completedRetraction_single_weightedCell parameters mode source cell value point

theorem completedRetraction_single_taylor {dimension : ℕ} (parameters : PhaseParameters)
    (mode : SpatialMode) (source cell : ℤ) (value : ComplexEuclidean dimension) (point : ClosedDisk) :
    weightedTaylorAt parameters cell point
      (completedRetraction parameters (coefficientSingle 4 (fibreMode (source,mode)) value)) =
      if source = cell then taylorSymbol point.val mode • value else 0 := by
  classical
  simp only [weightedTaylorAt,sub_apply,smul_apply,weightedValueAt_single,completedRetraction_single_weightedDerivative]
  by_cases same : source = cell
  · simp only [if_pos same,origin_val,map_zero,Complex.exp_zero,one_mul,smul_smul]
    rw [← sub_smul,← sub_smul,← sub_smul]
    congr 1
    rw [show taylorSymbol point.val mode = Complex.exp (imaginaryWaveLinear mode point.val) - 1 - imaginaryWaveLinear mode point.val from rfl,
      imaginaryWaveLinear_decompose]
    ring
  · simp only [if_neg same,smul_zero,sub_zero]

theorem completedRetraction_single_rotationRemainder {dimension : ℕ} (parameters : PhaseParameters)
    (mode : SpatialMode) (source cell : ℤ) (value : ComplexEuclidean dimension) (point : ClosedDisk) :
    weightedRotationRemainderAt parameters cell point
      (completedRetraction parameters (coefficientSingle 4 (fibreMode (source,mode)) value)) =
      if source = cell then rotationRemainderSymbol point.val mode • value else 0 := by
  classical
  simp only [weightedRotationRemainderAt,sub_apply,smul_apply,completedRetraction_single_weightedDerivative]
  by_cases same : source = cell
  · simp only [if_pos same,origin_val,map_zero,Complex.exp_zero,one_mul]
    simp only [← sub_smul,smul_smul]
    congr 1
    rw [show rotationRemainderSymbol point.val mode =
      (Complex.I * (rotationWave mode point.val : ℂ)) * (Complex.exp (imaginaryWaveLinear mode point.val) - 1) from rfl,
      ← imaginaryWaveLinear_rotation]
    ring
  · simp only [if_neg same,sub_zero,smul_zero]

end Grad.OriginalFlatAxisDecay
