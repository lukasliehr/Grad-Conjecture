import AXL11AngularFourier
import AXL12SeedTraceDerivative

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.GaugeCoefficients.Physical.Frame

variable {parameters : PhaseParameters}

theorem derivativeRowCoefficients_fourier (parameters : PhaseParameters)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coordinate : Fin 2) (angle : ℝ) :
    (∑' cell, axialPhase cell angle • Gauges.derivativeRowCoefficients seed coordinate cell) =
      (Gauges.planarComponentMap coordinate).comp (Gauges.transposeOperator
        (deriv (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3)) angle)) := by
  let mapping := (ContinuousLinearMap.compL ℂ (ComplexEuclidean 2) (ComplexEuclidean 2)
    (ComplexEuclidean 1) (Gauges.planarComponentMap coordinate)).comp Gauges.transposeContinuous
  have summable : Summable (fun cell => axialPhase cell angle • Seed.actualCells 2 seed cell) := by
    apply Summable.of_norm
    simpa only [norm_smul, norm_axialPhase, one_mul] using
      Gauges.seedCells_value_norm_summable parameters seed inside 2
  have terms (cell : ℤ) : axialPhase cell angle • Gauges.derivativeRowCoefficients seed coordinate cell =
      mapping (axialPhase cell angle • Seed.actualCells 2 seed cell) := by
    rw [map_smul]
    rfl
  rw [tsum_congr terms, ← mapping.map_tsum summable]
  have phase : cellExponential = axialPhase := by
    funext cell angle
    exact ((axialPhase_eq_character cell angle).trans (cellCharacter_coe cell angle)).symm
  have actual := (Seed.actual_seed_fourier parameters seed inside angle).2.2
  rw [phase] at actual
  rw [actual]
  rfl

theorem coreValue_gaugeCoordinate {dimension : ℕ} (coordinate : Fin 2)
    (field : ACore parameters dimension) (point : ClosedDisk) (angle : ℝ) :
    coreValue (Gauges.coordinateCore parameters coordinate field) point angle =
      point.val coordinate • coreValue field point angle := by
  have equality : Gauges.coordinateCore parameters coordinate field = coordinateCore parameters coordinate field := by
    apply Subtype.ext
    funext cell
    exact (coordinateJet_eq_realCoordinateJet coordinate (field.val cell)).symm
  rw [equality, coreValue_coordinate]

theorem coreValue_derivativeDot (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (field : ACore parameters 2) (point : ClosedDisk) (angle : ℝ) :
    coreValue (Gauges.derivativeDotCore parameters seed inside field) point angle =
      point.val 0 • Gauges.planarComponentMap 0
        (Gauges.transposeOperator (deriv (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3)) angle)
          (coreValue field point angle)) +
      point.val 1 • Gauges.planarComponentMap 1
        (Gauges.transposeOperator (deriv (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3)) angle)
          (coreValue field point angle)) := by
  simp only [Gauges.derivativeDotCore, LinearMap.add_apply, LinearMap.comp_apply, coreValue_add,
    coreValue_gaugeCoordinate, coreValue_smoothMultiplier, derivativeRowCoefficients_fourier parameters seed inside,
    ContinuousLinearMap.comp_apply]

def seedToroidalLinear (parameters : PhaseParameters) (seed : Seed.Parameters)
    (inside : seed ∈ Seed.parameterDomain) (coefficient : TameCoefficient parameters) : ACore parameters 1 :=
  Gauges.derivativeDotCore parameters seed inside
    (tameScalarMultiplier 2 coefficient (tameSeedPlanarField parameters seed inside))

theorem seedToroidalLinear_mean_zero (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) : angularCore parameters 0
      (seedToroidalLinear parameters seed inside coefficient) = 0 := by
  let matrix := harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3)
  apply angularCore_of_physical_quadratic _
    (fun angle => coefficientValue coefficient angle •
      ((Gauges.transposeOperator (deriv matrix angle)).comp (matrix angle)))
  · intro point angle
    apply PiLp.ext
    intro index
    fin_cases index
    rw [seedToroidalLinear, coreValue_derivativeDot, coreValue_tameScalarMultiplier,
      tameSeedPlanarField, coreValue_seedMatrix, coreValue_planarCoordinate]
    change _ = (quadraticMatrixJet (coefficientValue coefficient angle •
      ((Gauges.transposeOperator (deriv matrix angle)).comp (matrix angle)))).value point 0
    rw [quadraticMatrixJet_value]
    simp [Gauges.planarComponentMap, map_smul, matrix]
  · intro angle
    change Gauges.operatorTraceContinuous (coefficientValue coefficient angle •
      ((Gauges.transposeOperator (deriv matrix angle)).comp (matrix angle))) = 0
    rw [map_smul]
    change coefficientValue coefficient angle • Gauges.operatorTrace
      ((Gauges.transposeOperator (deriv matrix angle)).comp (matrix angle)) = 0
    rw [seedDerivative_trace_zero parameters seed inside angle, smul_zero]

end Grad.ChartAxisLift
