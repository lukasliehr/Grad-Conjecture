import AXL19LiftExtraction

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.ChartAxisSplit
open Grad.Q24Realization Grad.RealFixedRanges Grad.PhysicalCoordinates

variable {parameters : PhaseParameters}

theorem physicalChartState_capLiftState (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (sigma tangent : TangentCoefficient parameters) :
    physicalChartState parameters (smoothingChartCore parameters
      (capLiftState parameters radius positive seed inside coefficient sigma tangent)) =
      (tangent, capChartRemainder parameters radius positive seed inside coefficient tangent,
        capScalarAffine parameters radius positive sigma) := by
  change (tangent, toPhysicalCore parameters (toPhysicalCore parameters _), _) = _
  rw [toPhysicalCore_involutive]
  rfl

theorem chartDerivativeFamily_one_root (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (base direction : ChartState parameters) :
    chartDerivativeFamily parameters seed inside 1 base (fun _ => direction) =
      (chartAffineField parameters seed inside (rootDerivativeFamily 1 base.1 (fun _ => direction.1))
        direction.1 direction.2.1, direction.2.2) := by
  have root : chartTower 1 base.1 (chartTangentDirections (fun _ : Fin 1 => direction)) =
      rootDerivativeFamily 1 base.1 (fun _ => direction.1) := by
    apply chartTower_congr
    intro index bounded
    rw [chartTangentDirections_lt _ index bounded, rootDirections_lt _ index bounded]
  change (_, _) = (_, _)
  rw [root]
  rfl

/-- The actual first physical chart variation of E_b is exactly chi Q_b y,
including the transverse derivative of the root. -/
theorem chartDerivative_actualCapLift (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (base : ChartState parameters) (sigma tangent : TangentCoefficient parameters) :
    chartDerivativeFamily parameters seed inside 1 base
      (fun _ => physicalChartState parameters (smoothingChartCore parameters
        (actualCapLiftState parameters radius positive seed inside base.1 sigma tangent))) =
      (capAffineField parameters radius positive seed inside
          (rootDerivativeFamily 1 base.1 (fun _ => tangent)) tangent,
        capScalarAffine parameters radius positive sigma) := by
  unfold actualCapLiftState
  rw [physicalChartState_capLiftState, chartDerivativeFamily_one_root]
  exact Prod.ext (chartAffineField_capRemainder radius positive seed inside _ tangent) rfl

end Grad.ChartAxisLift
