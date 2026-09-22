import AXL13SeedToroidal

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.PhysicalCoordinates Grad.ChartAxisSplit

variable {parameters : PhaseParameters}

theorem derivativeDotCore_value_factor (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (first second : ACore parameters 2) (point : ClosedDisk) (factor : ℂ)
    (law : ∀ cell, (first.val cell).value point = factor • (second.val cell).value point)
    (cell : ℤ) :
    ((Gauges.derivativeDotCore parameters seed inside first).val cell).value point =
      factor • ((Gauges.derivativeDotCore parameters seed inside second).val cell).value point := by
  change (point.val 0 • ((Gauges.smoothMultiplier parameters _ _ first).val cell).value point +
    point.val 1 • ((Gauges.smoothMultiplier parameters _ _ first).val cell).value point) =
    factor • (point.val 0 • ((Gauges.smoothMultiplier parameters _ _ second).val cell).value point +
      point.val 1 • ((Gauges.smoothMultiplier parameters _ _ second).val cell).value point)
  rw [smoothMultiplier_value_factor _ _ first second point factor law cell,
    smoothMultiplier_value_factor _ _ first second point factor law cell, smul_add,
    smul_comm (point.val 0) factor, smul_comm (point.val 1) factor]

def seedToroidalCap (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) : ACore parameters 1 :=
  Gauges.derivativeDotCore parameters seed inside (tameScalarMultiplier 2 coefficient
    (Gauges.seedMatrixCore parameters seed inside (capPlanarCoordinate parameters radius positive)))

theorem seedToroidalCap_value_factor (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (cell : ℤ) (point : ClosedDisk) :
    ((seedToroidalCap parameters radius positive seed inside coefficient).val cell).value point =
      (radialCap radius positive point.val : ℂ) •
        ((seedToroidalLinear parameters seed inside coefficient).val cell).value point := by
  unfold seedToroidalCap seedToroidalLinear
  apply derivativeDotCore_value_factor
  intro index
  apply tameScalarMultiplier_value_factor
  intro inner
  rw [tameSeedPlanarField, Gauges.seedMatrixCore_eq_full, Gauges.seedMatrixCore_eq_full]
  exact smoothMultiplier_value_factor _ _ _ _ point _
    (fun index => capPlanarCoordinate_value_factor parameters radius positive index point) inner

theorem seedToroidalCap_mean_zero (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) :
    angularCore parameters 0 (seedToroidalCap parameters radius positive seed inside coefficient) = 0 := by
  apply acore_ext
  intro cell point
  rw [angularCore_factor 0 _ (seedToroidalLinear parameters seed inside coefficient)
    (fun point => (radialCap radius positive point.val : ℂ)) (radialCap_closedRadial radius positive)
    (seedToroidalCap_value_factor radius positive seed inside coefficient), seedToroidalLinear_mean_zero]
  simp

theorem tameCoordinateScalarField_mean_zero (coordinate : Fin 2) :
    angularCore parameters 0 (tameCoordinateScalarField parameters coordinate) = 0 := by
  apply Subtype.ext
  funext cell
  rw [tameCoordinateScalarField, singleton_coordinate, angularCore_apply, coordinateCore_val]
  by_cases same : cell = 0
  · subst cell
    exact angularClosedJet_coordinateConstant_zero coordinate _
  · simp only [singletonCore, if_neg same]
    have zero : coordinateJet coordinate (0 : ClosedJet 1) = 0 := by
      apply closedJet_eq_of_value_eq
      ext point index
      simp [coordinateJet_value]
    rw [zero]
    exact (angularClosedJetLinear 1 0).map_zero

theorem storedCapChartRemainder_toroidal (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters) :
    Gauges.toroidalCorrection parameters seed inside
      (storedCapChartRemainder parameters radius positive seed inside coefficient tangent) = 0 := by
  rw [Gauges.toroidalCorrection_apply, map_add, map_smul, storedCapChartRemainder_planar,
    map_sub, map_sub]
  change Gauges.toroidalInclusionCore parameters
    (angularCore parameters 0 (Gauges.toroidalPartCore parameters
      (storedCapChartRemainder parameters radius positive seed inside coefficient tangent)) +
      (parameters.length⁻¹ : ℂ) • (angularCore parameters 0 (seedToroidalCap parameters radius positive seed inside coefficient) -
        angularCore parameters 0 (seedToroidalLinear parameters seed inside coefficient))) = 0
  rw [seedToroidalCap_mean_zero, seedToroidalLinear_mean_zero, sub_self, smul_zero, add_zero]
  rw [storedCapChartRemainder, capChartRemainder, map_sub,
    storedCapAffineField_formula, storedAffineField_formula, map_sub, map_add, map_add,
    Gauges.toroidalPartCore_planarInclusionCore, Gauges.toroidalPartCore_planarInclusionCore,
    Gauges.toroidalPartCore_toroidalInclusionCore, Gauges.toroidalPartCore_toroidalInclusionCore,
    zero_add, zero_add, map_sub, capScalarAffine_mean_zero, map_add,
    scalarMultiplier_mean_zero _ _ (tameCoordinateScalarField_mean_zero 0),
    scalarMultiplier_mean_zero _ _ (tameCoordinateScalarField_mean_zero 1),
    add_zero, sub_self, map_zero]

end Grad.ChartAxisLift
