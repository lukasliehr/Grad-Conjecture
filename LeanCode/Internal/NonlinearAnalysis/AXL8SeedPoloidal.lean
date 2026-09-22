import AXL7PhysicalLinearGauge

noncomputable section

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.Frame

variable {parameters : PhaseParameters}

theorem coreValue_planarCoordinate (point : ClosedDisk) (angle : ℝ) :
    coreValue (tamePlanarCoordinateField parameters) point angle = complexDiskPoint point := by
  rw [tamePlanarCoordinateField, coreValue_add, singleton_coordinate, singleton_coordinate,
    coreValue_coordinate, coreValue_coordinate]
  change point.val 0 • coreValue (constantCore parameters (EuclideanSpace.single 0 1)) point angle +
    point.val 1 • coreValue (constantCore parameters (EuclideanSpace.single 1 1)) point angle = _
  rw [coreValue_constant, coreValue_constant]
  apply PiLp.ext
  intro index
  fin_cases index <;> simp [complexDiskPoint]

theorem coreValue_seedTranspose (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (field : ACore parameters 2) (point : ClosedDisk) (angle : ℝ) :
    coreValue (Gauges.seedTransposeCore parameters seed inside field) point angle =
      Gauges.transposeOperator (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3) angle)
        (coreValue field point angle) := by
  rw [Gauges.seedTransposeCore, coreValue_smoothMultiplier]
  have phase : Grad.GaugeCoefficients.Algebra.fourierPhase = axialPhase := by
    funext cell angle
    exact ((axialPhase_eq_character cell angle).trans (cellCharacter_coe cell angle)).symm
  rw [← phase, Gauges.seedTransposeCells_fourier parameters seed inside]

def seedPoloidalLinear (parameters : PhaseParameters) (seed : Seed.Parameters)
    (inside : seed ∈ Seed.parameterDomain) (coefficient : TameCoefficient parameters) : ACore parameters 2 :=
  Gauges.seedTransposeCore parameters seed inside
    (tameScalarMultiplier 2 coefficient (tameSeedPlanarField parameters seed inside))

theorem seedPoloidalLinear_mean_zero (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) :
    tangentialCore parameters (seedPoloidalLinear parameters seed inside coefficient) = 0 := by
  let matrix := fun angle => harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3) angle
  apply tangentialCore_of_physical_symmetric parameters _
    (fun angle => coefficientValue coefficient angle • ((Gauges.transposeOperator (matrix angle)).comp (matrix angle)))
  · intro point angle
    rw [seedPoloidalLinear, coreValue_seedTranspose, coreValue_tameScalarMultiplier,
      tameSeedPlanarField, coreValue_seedMatrix, coreValue_planarCoordinate, map_smul]
    rfl
  · intro angle
    rw [Gauges.operatorEntry_smul, Gauges.operatorEntry_smul, Gauges.operatorEntry_comp,
      Gauges.operatorEntry_comp, Gauges.transposeOperator_entry, Gauges.transposeOperator_entry,
      Gauges.transposeOperator_entry, Gauges.transposeOperator_entry]
    ring

def seedPoloidalCap (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) : ACore parameters 2 :=
  Gauges.seedTransposeCore parameters seed inside
    (tameScalarMultiplier 2 coefficient (Gauges.seedMatrixCore parameters seed inside
      (capPlanarCoordinate parameters radius positive)))

theorem seedPoloidalCap_value_factor (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (cell : ℤ) (point : ClosedDisk) :
    ((seedPoloidalCap parameters radius positive seed inside coefficient).val cell).value point =
      (radialCap radius positive point.val : ℂ) •
        ((seedPoloidalLinear parameters seed inside coefficient).val cell).value point := by
  unfold seedPoloidalCap seedPoloidalLinear Gauges.seedTransposeCore
  apply smoothMultiplier_value_factor
  intro index
  apply tameScalarMultiplier_value_factor
  intro inner
  rw [tameSeedPlanarField, Gauges.seedMatrixCore_eq_full, Gauges.seedMatrixCore_eq_full]
  exact smoothMultiplier_value_factor _ _ _ _ point _
    (fun index => capPlanarCoordinate_value_factor parameters radius positive index point) inner

theorem seedPoloidalCap_mean_zero (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) :
    tangentialCore parameters (seedPoloidalCap parameters radius positive seed inside coefficient) = 0 := by
  apply acore_ext
  intro cell point
  rw [tangentialCore_factor _ (seedPoloidalLinear parameters seed inside coefficient)
    (fun point => (radialCap radius positive point.val : ℂ)) (radialCap_closedRadial radius positive)
    (seedPoloidalCap_value_factor radius positive seed inside coefficient), seedPoloidalLinear_mean_zero]
  simp

end Grad.ChartAxisLift
