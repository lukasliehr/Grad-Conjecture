import AXL23AxisDataLift

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.ChartAxisSplit
open Grad.Q24Realization Grad.RealFixedRanges Grad.PhysicalCoordinates

variable {parameters : PhaseParameters}

theorem rootDerivativeFamily_one_explicit (base direction : TangentCoefficient parameters) :
    rootDerivativeFamily 1 base (fun _ => direction) =
      tameRootShifted 1 (tangentQuadratic base) * tangentDot base direction := by
  simp [rootDerivativeFamily, chartTower, chartTerms, chartTermChildren, singlesChildren,
    evalChartTerm, rootDirections]

theorem rootDerivativeFamily_one_add (base first second : TangentCoefficient parameters) :
    rootDerivativeFamily 1 base (fun _ => first + second) =
      rootDerivativeFamily 1 base (fun _ => first) + rootDerivativeFamily 1 base (fun _ => second) := by
  simp only [rootDerivativeFamily_one_explicit]
  rw [tangentDot_comm base, tangentDot_add_left, tangentDot_comm first, tangentDot_comm second, mul_add]

theorem rootDerivativeFamily_one_smul (base direction : TangentCoefficient parameters) (scalar : ℂ) :
    rootDerivativeFamily 1 base (fun _ => scalar • direction) =
      scalar • rootDerivativeFamily 1 base (fun _ => direction) := by
  simp only [rootDerivativeFamily_one_explicit]
  rw [tangentDot_comm base, tangentDot_smul_left, tangentDot_comm direction, tameMul_smul]

theorem capChartRemainder_add (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (firstC secondC : TameCoefficient parameters) (firstT secondT : TangentCoefficient parameters) :
    capChartRemainder parameters radius positive seed inside (firstC + secondC) (firstT + secondT) =
      capChartRemainder parameters radius positive seed inside firstC firstT +
        capChartRemainder parameters radius positive seed inside secondC secondT := by
  simp only [capChartRemainder, capAffineField, chartAffineField, tangentComponent_add,
    tameScalarMultiplier_add, map_add, add_zero]
  abel

theorem capChartRemainder_smul (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters) (scalar : ℂ) :
    capChartRemainder parameters radius positive seed inside (scalar • coefficient) (scalar • tangent) =
      scalar • capChartRemainder parameters radius positive seed inside coefficient tangent := by
  simp only [capChartRemainder, capAffineField, chartAffineField, tangentComponent_smul,
    tameScalarMultiplier_smul, smul_add, map_add, map_smul, add_zero, smul_sub]

theorem capScalarAffine_add (radius : ℝ) (positive : 0 < radius)
    (first second : TangentCoefficient parameters) :
    capScalarAffine parameters radius positive (first + second) =
      capScalarAffine parameters radius positive first + capScalarAffine parameters radius positive second := by
  simp only [capScalarAffine, tangentComponent_add, tameScalarMultiplier_add]
  abel

theorem capScalarAffine_smul (radius : ℝ) (positive : 0 < radius)
    (direction : TangentCoefficient parameters) (scalar : ℂ) :
    capScalarAffine parameters radius positive (scalar • direction) =
      scalar • capScalarAffine parameters radius positive direction := by
  simp only [capScalarAffine, tangentComponent_smul, tameScalarMultiplier_smul, smul_add]

/-- Complex linear extension of the literal lift with the real base fixed.
Reality is imposed only when restricting this map to the original real slice. -/
def capLiftLinear (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) (base : TangentCoefficient parameters) :
    (TangentCoefficient parameters × TangentCoefficient parameters) →ₗ[ℂ] Grad.SmoothingFamily.StateCore parameters where
  toFun data := actualCapLiftState parameters radius positive seed inside base data.1 data.2
  map_add' first second := by
    apply Prod.ext
    · exact map_add (tangentToStateAxis parameters) first.2 second.2
    · apply Prod.ext
      · change toPhysicalCore parameters (capChartRemainder parameters radius positive seed inside
          (rootDerivativeFamily 1 base (fun _ => first.2 + second.2)) (first.2 + second.2)) = _
        rw [rootDerivativeFamily_one_add, capChartRemainder_add, map_add]
        rfl
      · exact capScalarAffine_add radius positive first.1 second.1
  map_smul' scalar data := by
    apply Prod.ext
    · exact map_smul (tangentToStateAxis parameters) scalar data.2
    · apply Prod.ext
      · change toPhysicalCore parameters (capChartRemainder parameters radius positive seed inside
          (rootDerivativeFamily 1 base (fun _ => scalar • data.2)) (scalar • data.2)) = _
        rw [rootDerivativeFamily_one_smul, capChartRemainder_smul, map_smul]
        rfl
      · exact capScalarAffine_smul radius positive data.1 scalar

def axisDataCapLiftLinear (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) (base : TangentCoefficient parameters) :
    AxisData parameters →ₗ[ℂ] Grad.SmoothingFamily.StateCore parameters :=
  (capLiftLinear parameters radius positive seed inside base).comp
    ((axisToTangent parameters).prodMap (axisToTangent parameters))

end Grad.ChartAxisLift
