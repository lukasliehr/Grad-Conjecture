import OriginalEvaluationBound
import NGP01Reality

noncomputable section

set_option maxHeartbeats 800000

open Set
open scoped BigOperators ComplexConjugate

namespace Grad.CartesianState

open Grad.ClosedJets

local instance originalRealityCellPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

/-- The actual real-line lift of the exact disk–cell Fourier evaluation. -/
def originalPhysicalEvaluationLift {dimension grade : ℕ}
    (parameters : PhaseParameters)
    (field : GradeCore parameters dimension grade)
    (point : ClosedDisk) (cell : ℝ) : ComplexEuclidean dimension :=
  (originalPhysicalClosedJet parameters field.toCore).value
    (point, (cell : CellCircle))

theorem originalPhysicalEvaluationLift_eq_tsum
    {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension grade)
    (point : ClosedDisk) (coordinate : ℝ) :
    originalPhysicalEvaluationLift parameters field point coordinate =
      ∑' cell : ℤ,
        cellExponential cell coordinate •
          (field.toCore.1 cell).value point := by
  change ordinaryReconstructedValue
      (originalCoefficientCore parameters field.toCore)
        (point, (coordinate : CellCircle)) = _
  rw [ordinaryReconstructedValue_apply]
  apply tsum_congr
  intro cell
  rw [cellCharacter_coe]
  rfl

theorem originalPhysicalEvaluationLift_periodic
    {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension grade)
    (point : ClosedDisk) (cell : ℝ) :
    originalPhysicalEvaluationLift parameters field point (cell + 2 * Real.pi) =
      originalPhysicalEvaluationLift parameters field point cell := by
  unfold originalPhysicalEvaluationLift
  have circleEquality :
      (((cell + 2 * Real.pi : ℝ) : CellCircle)) =
        ((cell : ℝ) : CellCircle) :=
    AddCircle.coe_add_period (2 * Real.pi) cell
  rw [circleEquality]

/-- The physical Fourier evaluation of coefficientwise-real data is fixed by
coordinate conjugation at every disk point and every real cell coordinate. -/
theorem originalPhysicalEvaluationLift_real
    {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension grade)
    (reality : GradeCoreReality parameters field)
    (point : ClosedDisk) (coordinate : ℝ) :
    cartesianPhysicalConjugation dimension
        (originalPhysicalEvaluationLift parameters field point coordinate) =
      originalPhysicalEvaluationLift parameters field point coordinate := by
  let coefficients := originalCoefficientCore parameters field.toCore
  have coefficientNorms : Summable (fun cell : ℤ =>
      ‖(coefficients.1 cell).value‖) := by
    simpa [closedDerivative_zero_order] using
      physicalDerivative_series_summable coefficients
        emptyCartesianWord 0
  have vectorSeries : Summable (fun cell : ℤ =>
      cellExponential cell coordinate •
        (coefficients.1 cell).value point) := by
    apply Summable.of_norm_bounded coefficientNorms
    intro cell
    rw [norm_smul, cellExponential_norm, one_mul]
    exact (coefficients.1 cell).value.norm_coe_le_norm point
  rw [originalPhysicalEvaluationLift_eq_tsum]
  change cartesianPhysicalConjugation dimension
      (∑' cell : ℤ, cellExponential cell coordinate • (coefficients.1 cell).value point) =
    ∑' cell : ℤ, cellExponential cell coordinate • (coefficients.1 cell).value point
  apply PiLp.ext
  intro outputCoordinate
  rw [cartesianPhysicalConjugation_apply]
  let projection : ComplexEuclidean dimension →L[ℂ] ℂ :=
    PiLp.proj 2 (fun _ : Fin dimension => ℂ) outputCoordinate
  have componentSeries : Summable (fun cell : ℤ =>
      (cellExponential cell coordinate •
        (coefficients.1 cell).value point) outputCoordinate) := by
    apply Summable.of_norm_bounded coefficientNorms
    intro cell
    calc
      ‖(cellExponential cell coordinate •
          (coefficients.1 cell).value point) outputCoordinate‖ ≤
        ‖cellExponential cell coordinate •
          (coefficients.1 cell).value point‖ := PiLp.norm_apply_le _ _
      _ = ‖(coefficients.1 cell).value point‖ := by
        rw [norm_smul, cellExponential_norm, one_mul]
      _ ≤ ‖(coefficients.1 cell).value‖ :=
        (coefficients.1 cell).value.norm_coe_le_norm point
  have conjugated :=
    Complex.conjLIE.toContinuousLinearEquiv.toContinuousLinearMap.map_tsum
      componentSeries
  rw [show (∑' cell : ℤ,
        cellExponential cell coordinate •
          (coefficients.1 cell).value point) outputCoordinate =
      ∑' cell : ℤ,
        (cellExponential cell coordinate •
          (coefficients.1 cell).value point) outputCoordinate by
    exact projection.map_tsum vectorSeries]
  change conj (∑' cell : ℤ,
      (cellExponential cell coordinate •
        (coefficients.1 cell).value point) outputCoordinate) = _
  change conj (∑' cell : ℤ,
      (cellExponential cell coordinate •
        (coefficients.1 cell).value point) outputCoordinate) =
    ∑' cell : ℤ, conj ((cellExponential cell coordinate •
      (coefficients.1 cell).value point) outputCoordinate) at conjugated
  rw [conjugated]
  calc
    (∑' cell : ℤ,
        conj ((cellExponential cell coordinate •
          (coefficients.1 cell).value point) outputCoordinate)) =
      ∑' cell : ℤ,
        (cellExponential (-cell) coordinate •
          (coefficients.1 (-cell)).value point) outputCoordinate := by
      apply tsum_congr
      intro cell
      rw [PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul, map_mul,
        cellExponential_conjugate]
      have coefficientReality := reality (-cell) point outputCoordinate
      simpa only [neg_neg, coefficients, originalCoefficientCore] using
        congrArg (fun value : ℂ =>
          cellExponential (-cell) coordinate * value) coefficientReality
    _ = ∑' cell : ℤ,
        (cellExponential cell coordinate •
          (coefficients.1 cell).value point) outputCoordinate := by
      simpa only [Equiv.neg_apply] using
        (Equiv.neg ℤ).tsum_eq (fun cell : ℤ =>
          (cellExponential cell coordinate •
            (coefficients.1 cell).value point) outputCoordinate)

end Grad.CartesianState
