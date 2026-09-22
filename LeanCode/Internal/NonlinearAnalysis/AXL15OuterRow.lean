import AXL14ToroidalConstraint

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.BoundaryTrace
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.PhysicalCoordinates Grad.ChartAxisSplit Grad.Cor18

variable {parameters : PhaseParameters}

theorem scalarMultiplier_smoothMultiplier {inputDimension outputDimension : ℕ}
    [Nontrivial (ComplexEuclidean inputDimension)] [Nontrivial (ComplexEuclidean outputDimension)]
    (coefficient : TameCoefficient parameters)
    (operators : ℤ → ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension)
    (summable : ∀ grade, Summable (Multipliers.envelopeTerm parameters grade operators))
    (field : ACore parameters inputDimension) :
    Gauges.smoothMultiplier parameters operators summable (tameScalarMultiplier inputDimension coefficient field) =
      tameScalarMultiplier outputDimension coefficient (Gauges.smoothMultiplier parameters operators summable field) := by
  apply coreValue_ext
  intro point angle
  rw [coreValue_smoothMultiplier, coreValue_tameScalarMultiplier, coreValue_tameScalarMultiplier,
    coreValue_smoothMultiplier, map_smul]

theorem scalarMultiplier_singleton_value {dimension : ℕ} [Nontrivial (ComplexEuclidean dimension)]
    (coefficient : TameCoefficient parameters) (jet : ClosedJet dimension) (cell : ℤ) (point : ClosedDisk) :
    ((tameScalarMultiplier dimension coefficient (singletonCore parameters jet)).val cell).value point =
      coefficient.val cell • jet.value point := by
  rw [tameScalarMultiplier, ← (Gauges.smoothMultiplier_value_hasSum parameters _ _
    (singletonCore parameters jet) cell point).tsum_eq, tsum_eq_single cell]
  · rw [singletonCore_val, sub_self, if_pos rfl]
    rfl
  · intro other different
    rw [singletonCore_val, if_neg (show cell - other ≠ 0 by omega), closedJet_value_zero,
      ContinuousMap.zero_apply, map_zero]

theorem scalarMultiplier_planarCoordinate_value (coefficient : TameCoefficient parameters)
    (cell : ℤ) (point : ClosedDisk) :
    ((tameScalarMultiplier 2 coefficient (tamePlanarCoordinateField parameters)).val cell).value point =
      coefficient.val cell • complexDiskPoint point := by
  rw [tamePlanarCoordinateField, map_add, acore_val_add, closedJet_value_add, ContinuousMap.add_apply,
    scalarMultiplier_singleton_value, scalarMultiplier_singleton_value,
    coordinateJet_value, coordinateJet_value, constantValueJet_value, constantValueJet_value]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [complexDiskPoint]

theorem rowField_storedCapRemainder (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters) :
    rowField parameters seed inside (storedCapChartRemainder parameters radius positive seed inside coefficient tangent) =
      tameScalarMultiplier 2 coefficient (capPlanarCoordinate parameters radius positive) -
        tameScalarMultiplier 2 coefficient (tamePlanarCoordinateField parameters) := by
  change Gauges.seedInverseCore parameters seed inside
    (Gauges.planarPartCore parameters _) = _
  rw [storedCapChartRemainder_planar, map_sub, tameSeedPlanarField]
  have commute (field : ACore parameters 2) :
      Gauges.seedInverseCore parameters seed inside (tameScalarMultiplier 2 coefficient field) =
        tameScalarMultiplier 2 coefficient (Gauges.seedInverseCore parameters seed inside field) := by
    rw [Gauges.seedInverseCore_eq_full, Gauges.seedInverseCore_eq_full]
    exact scalarMultiplier_smoothMultiplier coefficient _ _ field
  rw [commute, commute, Gauges.seedInverse_seedMatrix_core, Gauges.seedInverse_seedMatrix_core]

theorem rowField_storedCapRemainder_boundary (radius : ℝ) (positive : 0 < radius)
    (bounded : radius ≤ 1) (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters)
    (cell : ℤ) (angle : CellCircle) :
    ((rowField parameters seed inside
      (storedCapChartRemainder parameters radius positive seed inside coefficient tangent)).val cell).value
        (boundaryDiskPoint angle) = -(coefficient.val cell • complexDiskPoint (boundaryDiskPoint angle)) := by
  rw [rowField_storedCapRemainder]
  change ((tameScalarMultiplier 2 coefficient (capPlanarCoordinate parameters radius positive)).val cell +
    -((tameScalarMultiplier 2 coefficient (tamePlanarCoordinateField parameters)).val cell)).value _ = _
  rw [closedJet_value_add, closedJet_value_neg, ContinuousMap.add_apply, ContinuousMap.neg_apply,
    tameScalarMultiplier_value_factor coefficient _ _ _ (radialCap radius positive (boundaryCirclePoint angle) : ℂ)
      (fun cell => capPlanarCoordinate_value_factor parameters radius positive cell (boundaryDiskPoint angle)),
    radialCap_zero radius positive (boundaryCirclePoint angle)
      (by rw [boundaryCirclePoint_norm]; linarith), Complex.ofReal_zero, zero_smul, zero_add,
    scalarMultiplier_planarCoordinate_value]

end Grad.ChartAxisLift
