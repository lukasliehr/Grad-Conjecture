import ACP13GenuineCoefficientRotation

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1400000
namespace Grad.ActualCurrentPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.NonlinearRange

/-- Differentiate the actual complete axial series on a closed-disk rotation
orbit. The summable majorant is cellwise, not a repeated global bound. -/
theorem coefficientPhysicalValue_orbit_hasDerivAt {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (column : PhysicalValue input)
    (axialAngle : ℝ) (point : ClosedDisk) (angle : ℝ) :
    HasDerivAt (fun time : ℝ => coefficientPhysicalValue (family 0) axialAngle
      (rotatedPoint time point) column)
      (∑' cell : ℤ, fourierPhase cell axialAngle •
        (rotationJet (coefficientColumnJet parameters family coherent cell column)).value
          (rotatedPoint angle point)) angle := by
  let term (cell : ℤ) (time : ℝ) := fourierPhase cell axialAngle •
    (coefficientColumnJet parameters family coherent cell column).value (rotatedPoint time point)
  let derivativeTerm (cell : ℤ) (time : ℝ) := fourierPhase cell axialAngle •
    (rotationJet (coefficientColumnJet parameters family coherent cell column)).value (rotatedPoint time point)
  have summable : Summable (fun cell : ℤ =>
      2 * coefficientCellBudget (family 1) cell * ‖column‖) :=
    ((coefficientCellBudget_summable (family 1)).mul_left 2).mul_right ‖column‖
  have each (cell : ℤ) (time : ℝ) : HasDerivAt (term cell) (derivativeTerm cell time) time :=
    (closedOrbit_hasDerivAt (coefficientColumnJet parameters family coherent cell column) point time).const_smul
      (fourierPhase cell axialAngle)
  have bound (cell : ℤ) (time : ℝ) : ‖derivativeTerm cell time‖ ≤
      2 * coefficientCellBudget (family 1) cell * ‖column‖ := by
    dsimp only [derivativeTerm]
    rw [norm_smul, fourierPhase_norm, one_mul]
    exact coefficientColumn_rotation_bound parameters family coherent cell column (rotatedPoint time point)
  have initial : Summable (fun cell : ℤ => term cell 0) :=
    (coefficientColumnJet_fourier parameters family coherent column axialAngle (rotatedPoint 0 point)).summable
  have actual := hasDerivAt_tsum summable each bound initial angle
  have equality : (fun time : ℝ => ∑' cell : ℤ, term cell time) =
      (fun time : ℝ => coefficientPhysicalValue (family 0) axialAngle (rotatedPoint time point) column) := by
    funext time
    exact (coefficientColumnJet_fourier parameters family coherent column axialAngle (rotatedPoint time point)).tsum_eq
  rw [equality] at actual
  exact actual

theorem coefficientPhysicalValue_rotation_series {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (column : PhysicalValue input)
    (axialAngle : ℝ) (point : ClosedDisk) :
    (∑' cell : ℤ, fourierPhase cell axialAngle •
      (rotationJet (coefficientColumnJet parameters family coherent cell column)).value point) =
      (point.val 0 : ℂ) •
        (∑' cell : ℤ, fourierPhase cell axialAngle •
          coefficientDerivative (family 1) cell secondSpatialIndex point) column -
      (point.val 1 : ℂ) •
        (∑' cell : ℤ, fourierPhase cell axialAngle •
          coefficientDerivative (family 1) cell firstSpatialIndex point) column := by
  have each (index : DerivativeIndex 1) : Summable (fun cell : ℤ =>
      fourierPhase cell axialAngle • coefficientDerivative (family 1) cell index point) := by
    apply Summable.of_norm
    simpa only [norm_smul, fourierPhase_norm, one_mul] using
      coefficientDerivative_point_norm_summable (unitDiskAdmissible parameters) (family 1) index point
  have columnSum (index : DerivativeIndex 1) : HasSum (fun cell : ℤ =>
      fourierPhase cell axialAngle • coefficientDerivative (family 1) cell index point column)
      ((∑' cell : ℤ, fourierPhase cell axialAngle • coefficientDerivative (family 1) cell index point) column) :=
    (ContinuousLinearMap.apply ℂ (PhysicalValue output) column).hasSum (each index).hasSum
  have sum := ((columnSum secondSpatialIndex).const_smul (point.val 0 : ℂ)).sub
    ((columnSum firstSpatialIndex).const_smul (point.val 1 : ℂ))
  apply HasSum.tsum_eq
  apply sum.congr_fun
  intro cell
  rw [coefficientColumn_rotation_value, smul_sub]
  congr 1 <;> exact smul_comm _ _ _

end Grad.ActualCurrentPrimitives
