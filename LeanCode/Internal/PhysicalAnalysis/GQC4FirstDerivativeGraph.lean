import GQC3SmoothFirstDerivative

noncomputable section

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem closedLift_add {Value : Type*} [AddZeroClass Value]
    (first second : ClosedDisk → Value) :
    closedDiskLift (fun point => first point + second point) =
      fun point => closedDiskLift first point + closedDiskLift second point := by
  funext point
  by_cases inside : point ∈ closedUnitDisk <;> simp [closedDiskLift, inside]

theorem closedLift_smul {Value : Type*} [AddCommGroup Value] [Module ℂ Value]
    (scalar : ℂ) (field : ClosedDisk → Value) :
    closedDiskLift (fun point => scalar • field point) = fun point => scalar • closedDiskLift field point := by
  funext point
  by_cases inside : point ∈ closedUnitDisk <;> simp [closedDiskLift, inside]

theorem closedLift_zero {Value : Type*} [Zero Value] :
    closedDiskLift (fun _ : ClosedDisk => (0 : Value)) = fun _ => 0 := by
  funext point
  by_cases inside : point ∈ closedUnitDisk <;> simp [closedDiskLift, inside]

def coefficientFirstDerivative {L sigma gamma ell : ℝ} {input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell 1 input output) (cell : ℤ) :
    C(ClosedDisk, SpatialPlane →L[ℝ] OperatorValue input output) :=
  planarDerivativeMap (coefficientDerivative coefficient cell (firstCoordinateIndex 0))
    (coefficientDerivative coefficient cell (firstCoordinateIndex 1))

theorem coefficientFirstDerivative_add {L sigma gamma ell : ℝ} {input output : ℕ}
    (first second : Coefficient L sigma gamma ell 1 input output) (cell : ℤ) :
    coefficientFirstDerivative (first + second) cell =
      coefficientFirstDerivative first cell + coefficientFirstDerivative second cell := by
  apply ContinuousMap.ext
  intro point
  apply ContinuousLinearMap.ext
  intro direction
  change planarDerivative (Value := OperatorValue input output) _ _ direction =
    planarDerivative (Value := OperatorValue input output) _ _ direction +
      planarDerivative (Value := OperatorValue input output) _ _ direction
  simp only [planarDerivative_apply, coefficientDerivative_add_apply, smul_add]
  abel

theorem coefficientFirstDerivative_smul {L sigma gamma ell : ℝ} {input output : ℕ}
    (scalar : ℂ) (coefficient : Coefficient L sigma gamma ell 1 input output) (cell : ℤ) :
    coefficientFirstDerivative (scalar • coefficient) cell = scalar • coefficientFirstDerivative coefficient cell := by
  apply ContinuousMap.ext
  intro point
  apply ContinuousLinearMap.ext
  intro direction
  change planarDerivative (Value := OperatorValue input output) _ _ direction =
    scalar • planarDerivative (Value := OperatorValue input output) _ _ direction
  simp only [planarDerivative_apply, coefficientDerivative_smul_apply, smul_add]
  rw [smul_comm (direction 0) scalar, smul_comm (direction 1) scalar]

theorem coefficientFirstDerivative_zero {L sigma gamma ell : ℝ} {input output : ℕ} (cell : ℤ) :
    coefficientFirstDerivative (0 : Coefficient L sigma gamma ell 1 input output) cell = 0 := by
  apply ContinuousMap.ext
  intro point
  apply ContinuousLinearMap.ext
  intro direction
  change planarDerivative (Value := OperatorValue input output) _ _ direction = 0
  have coordinateZero (index : DerivativeIndex 1) :
      coefficientDerivative (0 : Coefficient L sigma gamma ell 1 input output) cell index point = 0 :=
    smul_zero _
  rw [coordinateZero, coordinateZero, planarDerivative_apply, smul_zero, smul_zero, add_zero]

def CoefficientHasFirstDerivative {L sigma gamma ell : ℝ} {input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell 1 input output) (cell : ℤ) : Prop :=
  ∀ point : SpatialPlane, point ∈ openUnitDisk →
    HasFDerivAt (closedDiskLift (coefficientDerivative coefficient cell (zeroDerivativeIndexAt 1)))
      (closedDiskLift (coefficientFirstDerivative coefficient cell) point) point

theorem coefficientHasFirstDerivative_isClosed {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (input output : ℕ) (cell : ℤ) :
    IsClosed {coefficient : Coefficient L sigma gamma ell 1 input output |
      CoefficientHasFirstDerivative coefficient cell} := by
  have first := (coefficientClosedCoordinate admissible 1 input output cell (zeroDerivativeIndexAt 1)).continuous
  have second := planarDerivativeMap_continuous.comp
    ((coefficientClosedCoordinate admissible 1 input output cell (firstCoordinateIndex 0)).continuous.prodMk
      (coefficientClosedCoordinate admissible 1 input output cell (firstCoordinateIndex 1)).continuous)
  exact closedDerivativeGraph_isClosed.preimage (first.prodMk second)

theorem CoefficientHasFirstDerivative.add {L sigma gamma ell : ℝ} {input output : ℕ}
    {first second : Coefficient L sigma gamma ell 1 input output} {cell : ℤ}
    (firstCompatible : CoefficientHasFirstDerivative first cell)
    (secondCompatible : CoefficientHasFirstDerivative second cell) :
    CoefficientHasFirstDerivative (first + second) cell := by
  intro point inside
  have value : coefficientDerivative (first + second) cell (zeroDerivativeIndexAt 1) =
      coefficientDerivative first cell (zeroDerivativeIndexAt 1) +
        coefficientDerivative second cell (zeroDerivativeIndexAt 1) :=
    ContinuousMap.ext (fun point => coefficientDerivative_add_apply first second cell _ point)
  rw [value, coefficientFirstDerivative_add]
  change HasFDerivAt (closedDiskLift (fun point =>
    coefficientDerivative first cell (zeroDerivativeIndexAt 1) point +
      coefficientDerivative second cell (zeroDerivativeIndexAt 1) point))
    (closedDiskLift (fun point => coefficientFirstDerivative first cell point +
      coefficientFirstDerivative second cell point) point) point
  rw [closedLift_add (coefficientDerivative first cell (zeroDerivativeIndexAt 1))
    (coefficientDerivative second cell (zeroDerivativeIndexAt 1)),
    closedLift_add (coefficientFirstDerivative first cell) (coefficientFirstDerivative second cell)]
  exact (firstCompatible point inside).add (secondCompatible point inside)

theorem CoefficientHasFirstDerivative.smul {L sigma gamma ell : ℝ} {input output : ℕ}
    {coefficient : Coefficient L sigma gamma ell 1 input output} {cell : ℤ}
    (compatible : CoefficientHasFirstDerivative coefficient cell) (scalar : ℂ) :
    CoefficientHasFirstDerivative (scalar • coefficient) cell := by
  intro point inside
  have value : coefficientDerivative (scalar • coefficient) cell (zeroDerivativeIndexAt 1) =
      scalar • coefficientDerivative coefficient cell (zeroDerivativeIndexAt 1) :=
    ContinuousMap.ext (fun point => coefficientDerivative_smul_apply scalar coefficient cell _ point)
  rw [value, coefficientFirstDerivative_smul]
  change HasFDerivAt (closedDiskLift (fun point => scalar •
    coefficientDerivative coefficient cell (zeroDerivativeIndexAt 1) point))
    (closedDiskLift (fun point => scalar • coefficientFirstDerivative coefficient cell point) point) point
  rw [closedLift_smul scalar (coefficientDerivative coefficient cell (zeroDerivativeIndexAt 1)),
    closedLift_smul scalar (coefficientFirstDerivative coefficient cell)]
  exact (compatible point inside).const_smul scalar

theorem coefficientHasFirstDerivative_zero {L sigma gamma ell : ℝ} {input output : ℕ} (cell : ℤ) :
    CoefficientHasFirstDerivative (0 : Coefficient L sigma gamma ell 1 input output) cell := by
  intro point _
  rw [coefficientFirstDerivative_zero]
  have value : coefficientDerivative (0 : Coefficient L sigma gamma ell 1 input output)
      cell (zeroDerivativeIndexAt 1) = 0 := by
    apply ContinuousMap.ext
    intro point
    exact smul_zero _
  rw [value]
  change HasFDerivAt (closedDiskLift (fun _ => 0)) (closedDiskLift (fun _ => 0) point) point
  rw [closedLift_zero, closedLift_zero]
  exact hasFDerivAt_const (0 : OperatorValue input output) point

end Grad.GaugeCoefficients.Physical.Compensated
