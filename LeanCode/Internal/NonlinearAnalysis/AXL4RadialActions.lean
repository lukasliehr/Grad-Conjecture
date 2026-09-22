import AXL3PhysicalCutoff

noncomputable section

open MeasureTheory
open scoped Interval

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.GaugeCoefficients.Radial

def ClosedRadialFactor (factor : ClosedDisk → ℂ) : Prop :=
  ∀ (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (point : ClosedDisk),
    factor (orthogonalClosedPoint orthogonal point) = factor point

theorem radialCap_closedRadial (radius : ℝ) (positive : 0 < radius) :
    ClosedRadialFactor (fun point => (radialCap radius positive point.val : ℂ)) := by
  intro orthogonal point
  exact congrArg (fun value : ℝ => (value : ℂ)) (radialCap_isometry radius positive orthogonal point.val)

theorem ClosedRadialFactor.sub_one {factor : ClosedDisk → ℂ} (radial : ClosedRadialFactor factor) :
    ClosedRadialFactor (fun point => factor point - 1) := by
  intro orthogonal point
  exact congrArg (fun value : ℂ => value - 1) (radial orthogonal point)

theorem angularClosedJet_factor {dimension : ℕ} (mode : ℤ)
    (first second : ClosedJet dimension) (factor : ClosedDisk → ℂ)
    (radial : ClosedRadialFactor factor)
    (law : ∀ point, first.value point = factor point • second.value point) (point : ClosedDisk) :
    (angularClosedJet mode first).value point = factor point • (angularClosedJet mode second).value point := by
  rw [angularClosedJet_value, angularClosedJet_value]
  have integrands : (fun angle => angularCharacter mode angle • first.value (rotatedPoint angle point)) =
      fun angle => factor point • (angularCharacter mode angle • second.value (rotatedPoint angle point)) := by
    funext angle
    rw [law, show factor (rotatedPoint angle point) = factor point from radial (planeRotationEquiv angle) point,
      smul_comm]
  rw [integrands, intervalIntegral.integral_smul, smul_comm]

theorem equivariantAverageJet_factor (first second : ClosedJet 2) (factor : ClosedDisk → ℂ)
    (radial : ClosedRadialFactor factor)
    (law : ∀ point, first.value point = factor point • second.value point) (point : ClosedDisk) :
    (equivariantAverageJet first).value point = factor point • (equivariantAverageJet second).value point := by
  rw [equivariantAverageJet_value_helicity, equivariantAverageJet_value_helicity,
    angularClosedJet_factor 1 first second factor radial law,
    angularClosedJet_factor (-1) first second factor radial law, map_smul, map_smul, smul_add]

theorem tangentialJet_factor (first second : ClosedJet 2) (factor : ClosedDisk → ℂ)
    (radial : ClosedRadialFactor factor)
    (law : ∀ point, first.value point = factor point • second.value point) (point : ClosedDisk) :
    (tangentialJet first).value point = factor point • (tangentialJet second).value point := by
  rw [tangentialJet_value, tangentialJet_value,
    equivariantAverageJet_factor first second factor radial law,
    equivariantAverageJet_factor first second factor radial law,
    radial cartesianReflectionEquiv point, map_smul, ← smul_sub, smul_comm]

theorem angularCore_factor {parameters : PhaseParameters} {dimension : ℕ} (mode : ℤ)
    (first second : ACore parameters dimension) (factor : ClosedDisk → ℂ)
    (radial : ClosedRadialFactor factor)
    (law : ∀ cell point, (first.val cell).value point = factor point • (second.val cell).value point)
    (cell : ℤ) (point : ClosedDisk) :
    ((angularCore parameters mode first).val cell).value point =
      factor point • ((angularCore parameters mode second).val cell).value point :=
  angularClosedJet_factor mode (first.val cell) (second.val cell) factor radial (law cell) point

theorem tangentialCore_factor {parameters : PhaseParameters}
    (first second : ACore parameters 2) (factor : ClosedDisk → ℂ)
    (radial : ClosedRadialFactor factor)
    (law : ∀ cell point, (first.val cell).value point = factor point • (second.val cell).value point)
    (cell : ℤ) (point : ClosedDisk) :
    ((tangentialCore parameters first).val cell).value point =
      factor point • ((tangentialCore parameters second).val cell).value point :=
  tangentialJet_factor (first.val cell) (second.val cell) factor radial (law cell) point

theorem capAffineField_zero_outside {parameters : PhaseParameters} (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters)
    (cell : ℤ) (point : ClosedDisk) (outside : radius / 2 ≤ ‖point.val‖) :
    ((capAffineField parameters radius positive seed inside coefficient tangent).val cell).value point = 0 := by
  rw [capAffineField_value_factor, radialCap_zero radius positive point.val outside,
    Complex.ofReal_zero, zero_smul]

end Grad.ChartAxisLift
