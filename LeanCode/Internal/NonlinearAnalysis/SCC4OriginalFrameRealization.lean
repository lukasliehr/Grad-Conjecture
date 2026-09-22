import SCC3OriginalInverseFamily

noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger

theorem physicalScaledPoint_unit (point : ClosedDisk) :
    physicalScaledPoint 1 (by norm_num) (by norm_num) point = point := by
  apply Subtype.ext
  exact one_smul ℝ point.val

/-- Every original derivative is the actual convergent full-cell Fourier
sum. The factors commute only as scalar actions; the frame order is retained. -/
theorem originalDerivative_hasSum {dimension order : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (word : CartesianWord order) (cellOrder : ℕ)
    (angle : ℝ) (point : ClosedDisk) :
    HasSum (fun cell : ℤ => fourierPhase cell angle •
      (cellDerivativeFactor cell cellOrder • closedDerivative (field.val cell) order word point))
      (ordinaryDerivativeExtension (originalCoefficientCore parameters field) word cellOrder
        (point, (angle : CellCircle))) := by
  have evaluated := (ContinuousMap.evalCLM ℂ (point, (angle : CellCircle))).hasSum
    (ordinaryDerivativeDiskCellTerm_summable (originalCoefficientCore parameters field) word cellOrder).hasSum
  change HasSum (fun cell : ℤ => ordinaryDerivativeDiskCellTerm word cellOrder cell
    ((originalCoefficientCore parameters field).val cell) (point, (angle : CellCircle)))
    (ordinaryDerivativeExtension (originalCoefficientCore parameters field) word cellOrder
      (point, (angle : CellCircle))) at evaluated
  apply evaluated.congr_fun
  intro cell
  rw [ordinaryDerivativeDiskCellTerm_apply, cellCharacter_coe]
  exact smul_comm _ _ _

theorem originalReference_hasSum (angle : ℝ) (point : ClosedDisk) :
    HasSum (fun cell : ℤ => fourierPhase cell angle • referenceStateCell cell point)
      (referenceStateValue point) := by
  apply (hasSum_ite_eq (0 : ℤ) (referenceStateValue point)).congr_fun
  intro cell
  by_cases zero : cell = 0
  · subst cell
    simp [referenceStateCell, fourierPhase]
  · simp [referenceStateCell, zero]

theorem columnFrame_phase (a b c reference value : ComplexEuclidean 3) (phase scale epsilon : ℂ) :
    phase • (columnEmbedding 3 3 0 a + columnEmbedding 3 3 1 b +
      columnEmbedding 3 3 2 (scale • (c + epsilon • physicalRotation (reference + value)))) =
    columnEmbedding 3 3 0 (phase • a) + columnEmbedding 3 3 1 (phase • b) +
      columnEmbedding 3 3 2 (scale • (phase • c + epsilon •
        physicalRotation (phase • reference + phase • value))) := by
  simp only [smul_add, map_add, map_smul]
  module

theorem originalFrameCells_hasSum (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (angle : ℝ) (point : ClosedDisk) :
    HasSum (fun cell : ℤ => fourierPhase cell angle •
      frameDeviationCell parameters L epsilon (GradeCore.ofCoreLinear (grade := 4) field) cell point)
      (originalPhysicalFrameDeviation parameters L epsilon field angle point) := by
  have first := originalDerivative_hasSum parameters field firstPlanarDerivativeWord 0 angle point
  have second := originalDerivative_hasSum parameters field secondPlanarDerivativeWord 0 angle point
  have axial := originalDerivative_hasSum parameters field emptyCartesianWord 1 angle point
  have value := originalDerivative_hasSum parameters field emptyCartesianWord 0 angle point
  simp only [cellDerivativeFactor, pow_zero, one_smul] at first second value
  simp only [cellDerivativeFactor, pow_one, closedDerivative_zero_order] at axial
  simp only [closedDerivative_zero_order] at value
  have rotated := (physicalRotation.hasSum ((originalReference_hasSum angle point).add value)).const_smul
    (epsilon : ℂ)
  have third := (columnEmbedding 3 3 2).hasSum ((axial.add rotated).const_smul ((L : ℂ)⁻¹))
  have combined := (((columnEmbedding 3 3 0).hasSum first).add
    ((columnEmbedding 3 3 1).hasSum second)).add third
  change HasSum _ (originalPhysicalFrameDeviation parameters L epsilon field angle point) at combined
  apply combined.congr_fun
  intro cell
  exact columnFrame_phase
    (closedDerivative (field.val cell) 1 firstPlanarDerivativeWord point)
    (closedDerivative (field.val cell) 1 secondPlanarDerivativeWord point)
    ((Complex.I * (cell : ℂ)) • (field.val cell).value point)
    (referenceStateCell cell point) ((field.val cell).value point)
    (fourierPhase cell angle) ((L : ℂ)⁻¹) (epsilon : ℂ)

theorem unitFrameFamily_physicalValue (parameters : PhaseParameters) (epsilon : ℝ)
    (field : ACore parameters 3) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (actualFrameFamily parameters 1 1 epsilon field grade) angle point =
      originalPhysicalFrameDeviation parameters 1 epsilon field angle point := by
  unfold coefficientPhysicalValue
  have coefficient (cell : ℤ) :
      coefficientDerivative (actualFrameFamily parameters 1 1 epsilon field grade)
        cell (zeroDerivativeIndexAt grade) point =
      frameDeviationCell parameters 1 epsilon (GradeCore.ofCoreLinear (grade := 4) field) cell point := by
    have actual := actualFrameDeviationCoefficient_value parameters (unitDiskAdmissible parameters)
      epsilon (GradeCore.ofCoreLinear (grade := grade + 4) field) cell point
    rw [physicalScaledPoint_unit] at actual
    exact actual
  simp_rw [coefficient]
  exact (originalFrameCells_hasSum parameters 1 epsilon field angle point).tsum_eq

theorem originalPhysicalFrameDeviation_columnScale (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (angle : ℝ) (point : ClosedDisk) :
    (originalPhysicalFrameDeviation parameters 1 epsilon field angle point).comp (physicalColumnScale L) =
      originalPhysicalFrameDeviation parameters L epsilon field angle point := by
  apply ContinuousLinearMap.ext
  intro value
  rw [ContinuousLinearMap.comp_apply, physicalColumnScale_apply]
  apply PiLp.ext
  intro coordinate
  simp only [originalPhysicalFrameDeviation, add_apply, columnEmbedding_apply, PiLp.add_apply,
    PiLp.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, smul_eq_mul, Complex.ofReal_one, inv_one, one_smul]
  dsimp
  ring

/-- Exact same-point identity with the repaired BS28 physical frame. -/
theorem originalFrameFamily_physicalValue (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (originalFrameFamily parameters L epsilon field grade) angle point =
      originalPhysicalFrameDeviation parameters L epsilon field angle point := by
  unfold originalFrameFamily composeFamily
  rw [family_physicalValue_comp (unitDiskAdmissible parameters) _ _
    (actualFrameFamily_coherent parameters (unitDiskAdmissible parameters) epsilon field)
    (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 (physicalColumnScale L)),
    constantFamily_physicalValue (unitDiskAdmissible parameters), unitFrameFamily_physicalValue,
    originalPhysicalFrameDeviation_columnScale]

end Grad.SourceCollarCoefficients
