import AXL2AffineRemainder

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.ChartAxisSplit

variable {parameters : PhaseParameters}

theorem radialCapJet_value_factor {dimension : ℕ} (radius : ℝ) (positive : 0 < radius)
    (coordinate : Fin 2) (vector : ComplexEuclidean dimension) (point : ClosedDisk) :
    (radialCapJet radius positive coordinate vector).value point =
      (radialCap radius positive point.val : ℂ) •
        (coordinateJet coordinate (constantValueJet vector)).value point := by
  rw [radialCapJet, globalClosedJet_value, coordinateJet_value, constantValueJet_value,
    Complex.coe_smul, radialCapLinearField, mul_smul]
  rfl

theorem capCoordinateCore_value_factor (parameters : PhaseParameters) (radius : ℝ)
    (positive : 0 < radius) {dimension : ℕ} (coordinate : Fin 2)
    (vector : ComplexEuclidean dimension) (cell : ℤ) (point : ClosedDisk) :
    ((capCoordinateCore parameters radius positive coordinate vector).val cell).value point =
      (radialCap radius positive point.val : ℂ) •
        ((singletonCore parameters (coordinateJet coordinate (constantValueJet vector))).val cell).value point := by
  rw [capCoordinateCore, singletonCore_val, singletonCore_val]
  by_cases zeroCell : cell = 0
  · simp only [if_pos zeroCell]
    exact radialCapJet_value_factor radius positive coordinate vector point
  · simp only [if_neg zeroCell, closedJet_value_zero, ContinuousMap.zero_apply, smul_zero]

theorem capPlanarCoordinate_value_factor (parameters : PhaseParameters) (radius : ℝ)
    (positive : 0 < radius) (cell : ℤ) (point : ClosedDisk) :
    ((capPlanarCoordinate parameters radius positive).val cell).value point =
      (radialCap radius positive point.val : ℂ) •
        ((tamePlanarCoordinateField parameters).val cell).value point := by
  rw [capPlanarCoordinate, tamePlanarCoordinateField, acore_val_add, acore_val_add,
    closedJet_value_add, closedJet_value_add, ContinuousMap.add_apply, ContinuousMap.add_apply,
    capCoordinateCore_value_factor, capCoordinateCore_value_factor, smul_add]

theorem smoothMultiplier_value_factor {inputDimension outputDimension : ℕ}
    (coefficients : ℤ → ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension)
    (summable : ∀ grade, Summable (Multipliers.envelopeTerm parameters grade coefficients))
    (first second : ACore parameters inputDimension) (point : ClosedDisk) (factor : ℂ)
    (law : ∀ cell, ((first.val cell).value point) = factor • ((second.val cell).value point))
    (cell : ℤ) :
    ((Gauges.smoothMultiplier parameters coefficients summable first).val cell).value point =
      factor • ((Gauges.smoothMultiplier parameters coefficients summable second).val cell).value point := by
  rw [← (Gauges.smoothMultiplier_value_hasSum parameters coefficients summable first cell point).tsum_eq,
    ← (Gauges.smoothMultiplier_value_hasSum parameters coefficients summable second cell point).tsum_eq,
    ← tsum_const_smul'']
  apply tsum_congr
  intro shift
  rw [law, map_smul]

theorem tameScalarMultiplier_value_factor {dimension : ℕ} [Nontrivial (ComplexEuclidean dimension)]
    (coefficient : TameCoefficient parameters) (first second : ACore parameters dimension)
    (point : ClosedDisk) (factor : ℂ)
    (law : ∀ cell, ((first.val cell).value point) = factor • ((second.val cell).value point))
    (cell : ℤ) :
    ((tameScalarMultiplier dimension coefficient first).val cell).value point =
      factor • ((tameScalarMultiplier dimension coefficient second).val cell).value point :=
  smoothMultiplier_value_factor _ _ first second point factor law cell

theorem capSeedField_value_factor (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) (cell : ℤ) (point : ClosedDisk) :
    ((capSeedField parameters radius positive seed inside).val cell).value point =
      (radialCap radius positive point.val : ℂ) • ((tameSeedField parameters seed inside).val cell).value point := by
  rw [capSeedField, tameSeedField, tameSeedPlanarField, valueMapCore_val, valueMapCore_val,
    valueMapJet_value, valueMapJet_value, Gauges.seedMatrixCore_eq_full, Gauges.seedMatrixCore_eq_full,
    smoothMultiplier_value_factor _ _ _ _ point (radialCap radius positive point.val : ℂ)
      (fun cell => capPlanarCoordinate_value_factor parameters radius positive cell point), map_smul]

theorem capAffineField_value_factor (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters)
    (cell : ℤ) (point : ClosedDisk) :
    ((capAffineField parameters radius positive seed inside coefficient tangent).val cell).value point =
      (radialCap radius positive point.val : ℂ) •
        ((chartAffineField parameters seed inside coefficient tangent 0).val cell).value point := by
  rw [capAffineField, chartAffineField, add_zero, acore_val_add, acore_val_add,
    closedJet_value_add, closedJet_value_add, ContinuousMap.add_apply, ContinuousMap.add_apply,
    valueMapCore_val, valueMapCore_val, valueMapJet_value, valueMapJet_value,
    acore_val_add, acore_val_add, closedJet_value_add, closedJet_value_add,
    ContinuousMap.add_apply, ContinuousMap.add_apply]
  rw [tameScalarMultiplier_value_factor coefficient _ _ point (radialCap radius positive point.val : ℂ)
      (fun cell => capSeedField_value_factor radius positive seed inside cell point),
    tameScalarMultiplier_value_factor (tangentComponent tangent 0)
      (capScalarCoordinate parameters radius positive 0) (tameCoordinateScalarField parameters 0) point
      (radialCap radius positive point.val : ℂ)
      (fun cell => capCoordinateCore_value_factor parameters radius positive 0 _ cell point),
    tameScalarMultiplier_value_factor (tangentComponent tangent 1)
      (capScalarCoordinate parameters radius positive 1) (tameCoordinateScalarField parameters 1) point
      (radialCap radius positive point.val : ℂ)
      (fun cell => capCoordinateCore_value_factor parameters radius positive 1 _ cell point),
    ← smul_add, map_smul, smul_add]

theorem capChartRemainder_value_factor (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters)
    (cell : ℤ) (point : ClosedDisk) :
    ((capChartRemainder parameters radius positive seed inside coefficient tangent).val cell).value point =
      ((radialCap radius positive point.val : ℂ) - 1) •
        ((chartAffineField parameters seed inside coefficient tangent 0).val cell).value point := by
  change ((capAffineField parameters radius positive seed inside coefficient tangent).val cell +
    -((chartAffineField parameters seed inside coefficient tangent 0).val cell)).value point = _
  rw [closedJet_value_add, closedJet_value_neg, ContinuousMap.add_apply, ContinuousMap.neg_apply,
    capAffineField_value_factor, sub_smul, one_smul]
  rfl

end Grad.ChartAxisLift
