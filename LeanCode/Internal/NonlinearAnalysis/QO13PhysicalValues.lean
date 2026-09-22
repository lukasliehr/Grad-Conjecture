import QO12FourierNormalization
import QO11LiteralReality

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 800000

open scoped ComplexConjugate BigOperators

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.CompletedReality

variable {parameters : PhaseParameters}

def coreValue {dimension : ℕ} (field : ACore parameters dimension)
    (point : ClosedDisk) (angle : ℝ) : ComplexEuclidean dimension :=
  ∑' cell, axialPhase cell angle • (field.val cell).value point

theorem coreValue_summable {dimension : ℕ} (field : ACore parameters dimension)
    (point : ClosedDisk) (angle : ℝ) :
    Summable (fun cell => axialPhase cell angle • (field.val cell).value point) := by
  apply Summable.of_norm
  simpa only [norm_smul, norm_axialPhase, one_mul] using
    Gauges.originalValueNorm_summable parameters field point

theorem coreValue_ext {dimension : ℕ} {first second : ACore parameters dimension}
    (equalValues : ∀ point angle, coreValue first point angle = coreValue second point angle) :
    first = second := by
  apply acore_ext
  intro cell point
  have equality := axialSeries_ext (fun cell => (first.val cell).value point)
    (fun cell => (second.val cell).value point)
    (Gauges.originalValueNorm_summable parameters first point)
    (Gauges.originalValueNorm_summable parameters second point) (equalValues point)
  exact congrFun equality cell

theorem coreValue_add {dimension : ℕ} (first second : ACore parameters dimension)
    (point : ClosedDisk) (angle : ℝ) :
    coreValue (first + second) point angle = coreValue first point angle + coreValue second point angle := by
  unfold coreValue
  simp_rw [acore_add_value, smul_add]
  exact (coreValue_summable first point angle).tsum_add (coreValue_summable second point angle)

theorem coreValue_smul {dimension : ℕ} (scalar : ℂ) (field : ACore parameters dimension)
    (point : ClosedDisk) (angle : ℝ) :
    coreValue (scalar • field) point angle = scalar • coreValue field point angle := by
  unfold coreValue
  simp_rw [acore_smul_value, smul_comm (axialPhase _ angle) scalar]
  exact tsum_const_smul'' scalar

theorem coreValue_valueMap {inputDimension outputDimension : ℕ}
    (mapping : ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension)
    (field : ACore parameters inputDimension) (point : ClosedDisk) (angle : ℝ) :
    coreValue (valueMapCore parameters mapping field) point angle = mapping (coreValue field point angle) := by
  unfold coreValue
  simp_rw [valueMapCore_value, ← map_smul]
  exact (mapping.map_tsum (coreValue_summable field point angle)).symm

theorem coreValue_constant {dimension : ℕ} (vector : ComplexEuclidean dimension)
    (point : ClosedDisk) (angle : ℝ) : coreValue (constantCore parameters vector) point angle = vector := by
  unfold coreValue
  rw [tsum_eq_single 0]
  · rw [constantCore_value_zero, axialPhase_zero, one_smul]
  · intro cell nonzero
    rw [constantCore_value_ne vector nonzero, smul_zero]

theorem coreValue_coordinate {dimension : ℕ} (coordinate : Fin 2)
    (field : ACore parameters dimension) (point : ClosedDisk) (angle : ℝ) :
    coreValue (coordinateCore parameters coordinate field) point angle =
      point.val coordinate • coreValue field point angle := by
  unfold coreValue
  simp_rw [Grad.AxisSplit.coordinateCore_val, coordinateJet_value,
    smul_comm (axialPhase _ angle) (point.val coordinate)]
  exact tsum_const_smul'' (point.val coordinate)

theorem coreValue_smoothMultiplier {inputDimension outputDimension : ℕ}
    (coefficients : ℤ → ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension)
    (summable : ∀ grade, Summable (Multipliers.envelopeTerm parameters grade coefficients))
    (field : ACore parameters inputDimension) (point : ClosedDisk) (angle : ℝ) :
    coreValue (Gauges.smoothMultiplier parameters coefficients summable field) point angle =
      (∑' cell, axialPhase cell angle • coefficients cell) (coreValue field point angle) := by
  have physical := Gauges.smoothMultiplier_physical parameters coefficients summable field point angle
  rw [originalPhysicalEvaluationLift_eq_tsum, originalPhysicalEvaluationLift_eq_tsum] at physical
  have phase : cellExponential = axialPhase := by
    funext cell angle
    exact (axialPhase_eq_character cell angle).trans (cellCharacter_coe cell angle) |>.symm
  simpa only [phase, coreValue, GradeCore.toCore_ofCore] using physical

def pairCellAssignments (cell : ℤ) : ℤ ≃ CellAssignments 2 cell where
  toFun shift := ⟨![shift, cell - shift], by simp⟩
  invFun assignment := assignment.val 0
  left_inv _ := rfl
  right_inv assignment := by
    apply Subtype.ext
    funext index
    have total := assignment.property
    rw [Fin.sum_univ_two] at total
    fin_cases index
    · rfl
    · change cell - assignment.val 0 = assignment.val 1
      omega

theorem productCoefficientValue_pair {inputDimension outputDimension : ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin 2 => ComplexEuclidean inputDimension) (ComplexEuclidean outputDimension))
    (first second : ACore parameters inputDimension) (cell : ℤ) (point : ClosedDisk) :
    productCoefficientValue multiplication ![first, second] cell point =
      ∑' shift, multiplication ![(first.val shift).value point, (second.val (cell - shift)).value point] := by
  unfold productCoefficientValue
  rw [← (pairCellAssignments cell).tsum_eq]
  apply tsum_congr
  intro shift
  congr 1
  funext index
  fin_cases index <;> rfl

end Grad.NonlinearRange
