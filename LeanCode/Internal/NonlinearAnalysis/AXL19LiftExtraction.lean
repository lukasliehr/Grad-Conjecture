import AXL18LiftReality

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.ChartAxisSplit
open Grad.Q24Realization Grad.RealFixedRanges

variable {parameters : PhaseParameters}

theorem capScalarMultiplier_originPartial (radius : ℝ) (positive : 0 < radius)
    (coefficient : TameCoefficient parameters) (coordinate direction : Fin 2) (cell : ℤ) :
    originPartial direction ((tameScalarMultiplier 1 coefficient
      (capScalarCoordinate parameters radius positive coordinate)).val cell) =
      if direction = coordinate then coefficient.val cell • EuclideanSpace.single 0 1 else 0 := by
  have zeroJets := tameScalarMultiplier_zeroJets coefficient _
    (capScalarCoordinate_difference_zeroJets parameters radius positive coordinate) cell
  have derivative := zeroJets 1 le_rfl (fun _ => direction)
  change originPartial direction ((tameScalarMultiplier 1 coefficient
    (capScalarCoordinate parameters radius positive coordinate -
      tameCoordinateScalarField parameters coordinate)).val cell) = 0 at derivative
  rw [map_sub, acore_val_sub, originPartial_sub, sub_eq_zero] at derivative
  exact derivative.trans (tameScalarMultiplier_coordinate_originPartial coefficient coordinate direction cell)

theorem capScalarAffine_originGradient (radius : ℝ) (positive : 0 < radius)
    (sigma : TangentCoefficient parameters) (cell : ℤ) :
    scalarOriginGradient (capScalarAffine parameters radius positive sigma) cell = sigma.val cell := by
  unfold scalarOriginGradient capScalarAffine
  simp only [acore_val_add, originPartial_add, capScalarMultiplier_originPartial]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [tangentComponent_val]

/-- The actual cap lift uses the derivative of the already constructed root;
there is no auxiliary coefficient assumption in this definition. -/
def actualCapLiftState (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (base sigma tangent : TangentCoefficient parameters) : Grad.SmoothingFamily.StateCore parameters :=
  capLiftState parameters radius positive seed inside
    (rootDerivativeFamily 1 base (fun _ => tangent)) sigma tangent

theorem actualCapLiftState_mem (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (base sigma tangent : TangentCoefficient parameters)
    (realBase : RealTangent base) (axis : RootAxisCondition base)
    (realS : RealTangent sigma) (realT : RealTangent tangent) :
    actualCapLiftState parameters radius positive seed inside base sigma tangent ∈
      stateSmoothRange parameters seed inside :=
  capLiftState_mem radius positive bounded seed inside _
    (rootDerivativeFamily_one_real base tangent realBase realT axis) sigma tangent realS realT

def actualCapLift (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (base sigma tangent : TangentCoefficient parameters)
    (realBase : RealTangent base) (axis : RootAxisCondition base)
    (realS : RealTangent sigma) (realT : RealTangent tangent) : stateSmoothRange parameters seed inside :=
  ⟨actualCapLiftState parameters radius positive seed inside base sigma tangent,
    actualCapLiftState_mem radius positive bounded seed inside base sigma tangent realBase axis realS realT⟩

theorem chartKappa_actualCapLift (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (base sigma tangent : TangentCoefficient parameters)
    (realBase : RealTangent base) (axis : RootAxisCondition base)
    (realS : RealTangent sigma) (realT : RealTangent tangent) :
    chartKappa parameters seed inside
      (actualCapLift parameters radius positive bounded seed inside base sigma tangent realBase axis realS realT) =
      (sigma.val, tangent.val) := by
  apply Prod.ext
  · funext cell
    exact capScalarAffine_originGradient radius positive sigma cell
  · rfl

end Grad.ChartAxisLift
