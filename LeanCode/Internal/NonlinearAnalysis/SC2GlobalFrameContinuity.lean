import SC2GlobalFrameInverse

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 900000

open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace Grad.SourceCollar

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState Grad.NonlinearProduct
open Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger

theorem continuous_matrix_det {X : Type*} [TopologicalSpace X]
    (matrix : X → Matrix (Fin 3) (Fin 3) ℂ) (continuous : Continuous matrix) :
    Continuous (fun point => (matrix point).det) := by
  simp_rw [Matrix.det_fin_three]
  fun_prop

theorem continuous_matrix_adjugate {X : Type*} [TopologicalSpace X]
    (matrix : X → Matrix (Fin 3) (Fin 3) ℂ) (continuous : Continuous matrix) :
    Continuous (fun point => (matrix point).adjugate) := by
  simp_rw [Matrix.adjugate_fin_three]
  fun_prop

theorem continuous_matrix_inv {X : Type*} [TopologicalSpace X]
    (matrix : X → Matrix (Fin 3) (Fin 3) ℂ) (continuous : Continuous matrix)
    (nonzero : ∀ point, (matrix point).det ≠ 0) :
    Continuous (fun point => (matrix point)⁻¹) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact (continuous_matrix_det matrix continuous).inv₀ nonzero |>.smul
    (continuous_matrix_adjugate matrix continuous)

theorem originalPhysicalFrameMatrix_continuous
    (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (axialAngle : ℝ) :
    Continuous (fun point : ClosedDisk =>
      originalPhysicalFrameMatrix parameters L epsilon field axialAngle point) := by
  let coefficients := originalCoefficientCore parameters field
  let location : ClosedDisk → DiskCellDomain :=
    fun point => (point, (axialAngle : CellCircle))
  have locationContinuous : Continuous location := continuous_id.prodMk continuous_const
  have firstContinuous : Continuous (fun point =>
      ordinaryDerivativeExtension coefficients firstPlanarDerivativeWord 0 (location point)) :=
    (ordinaryDerivativeExtension coefficients firstPlanarDerivativeWord 0).continuous.comp
      locationContinuous
  have secondContinuous : Continuous (fun point =>
      ordinaryDerivativeExtension coefficients secondPlanarDerivativeWord 0 (location point)) :=
    (ordinaryDerivativeExtension coefficients secondPlanarDerivativeWord 0).continuous.comp
      locationContinuous
  have axialContinuous : Continuous (fun point =>
      ordinaryDerivativeExtension coefficients emptyCartesianWord 1 (location point)) :=
    (ordinaryDerivativeExtension coefficients emptyCartesianWord 1).continuous.comp
      locationContinuous
  have valueContinuous : Continuous (fun point =>
      ordinaryDerivativeExtension coefficients emptyCartesianWord 0 (location point)) :=
    (ordinaryDerivativeExtension coefficients emptyCartesianWord 0).continuous.comp
      locationContinuous
  have referenceContinuous : Continuous referenceStateValue := by
    unfold referenceStateValue
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp
    apply continuous_pi
    intro coordinate
    fin_cases coordinate <;> simp <;> fun_prop
  have deviationContinuous : Continuous (fun point =>
      originalPhysicalFrameDeviation parameters L epsilon field axialAngle point) := by
    change Continuous (fun point =>
      columnEmbedding 3 3 0
          (ordinaryDerivativeExtension coefficients firstPlanarDerivativeWord 0 (location point)) +
        columnEmbedding 3 3 1
          (ordinaryDerivativeExtension coefficients secondPlanarDerivativeWord 0 (location point)) +
        columnEmbedding 3 3 2 ((L : ℂ)⁻¹ •
          (ordinaryDerivativeExtension coefficients emptyCartesianWord 1 (location point) +
            (epsilon : ℂ) • physicalRotation
              (referenceStateValue point +
                ordinaryDerivativeExtension coefficients emptyCartesianWord 0 (location point)))))
    fun_prop
  have mappingContinuous : Continuous (fun point => referenceFrame +
      originalPhysicalFrameDeviation parameters L epsilon field axialAngle point) :=
    continuous_const.add deviationContinuous
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  unfold originalPhysicalFrameMatrix operatorMatrix
  fun_prop

theorem originalPhysicalFrameMatrix_polar_continuous
    (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (radius : ℝ) (bounded : |radius| ≤ 1) (axialAngle : ℝ) :
    Continuous (fun polarAngle => originalPhysicalFrameMatrix parameters L epsilon field
      axialAngle (polarClosedPoint radius bounded polarAngle)) := by
  exact (originalPhysicalFrameMatrix_continuous parameters L epsilon field axialAngle).comp
    (Grad.GaugeCoefficients.Radial.continuous_rotatedPoint_joint.comp
      (continuous_id.prodMk continuous_const))

theorem originalPhysicalSignedCofactor_polar_continuous_of_low
    (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (low : originalGradeNorm 4 field + |epsilon| ≤ originalFrameLowRadius parameters L)
    (radius : ℝ) (bounded : |radius| ≤ 1) (axialAngle : ℝ) :
    Continuous (fun polarAngle => originalPhysicalSignedCofactor parameters L epsilon field
      axialAngle (polarClosedPoint radius bounded polarAngle)) := by
  let matrix : ℝ → Matrix (Fin 3) (Fin 3) ℂ := fun polarAngle =>
    originalPhysicalFrameMatrix parameters L epsilon field axialAngle
      (polarClosedPoint radius bounded polarAngle)
  have matrixContinuous : Continuous matrix :=
    originalPhysicalFrameMatrix_polar_continuous parameters L epsilon field radius bounded axialAngle
  have determinantNonzero : ∀ polarAngle, (matrix polarAngle).det ≠ 0 := by
    intro polarAngle
    exact (originalPhysicalFrameMatrix_isUnit_det_of_low parameters L epsilon field low axialAngle
      (polarClosedPoint radius bounded polarAngle)).ne_zero
  have inverseContinuous : Continuous (fun polarAngle => (matrix polarAngle)⁻¹) :=
    continuous_matrix_inv matrix matrixContinuous determinantNonzero
  unfold originalPhysicalSignedCofactor
  change Continuous (fun polarAngle => (matrix polarAngle).det •
    ((matrix polarAngle)⁻¹ * ((matrix polarAngle)⁻¹).transpose))
  fun_prop

end Grad.SourceCollar
