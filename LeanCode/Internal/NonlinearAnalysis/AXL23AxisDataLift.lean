import AXL22RootFormula

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped ComplexConjugate

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.ChartAxisSplit
open Grad.Q24Realization Grad.RealFixedRanges Grad.PhysicalCoordinates

variable {parameters : PhaseParameters}

/-- Identity of the literal all-grade axis coefficients, with no change
to their weights or admissible sequences. -/
def axisToTangent (parameters : PhaseParameters) : TCore parameters →ₗ[ℂ] TangentCoefficient parameters where
  toFun family := ⟨family.val, fun grade => by
    have summable := (memlp_iff_summable_sq _).mp (family.property grade)
    apply summable.congr
    intro cell
    rw [tangentTerm_eq_axis]
    change ‖Grad.AxisSplit.axisWeight parameters grade cell • family.val cell‖ ^ 2 = _
    rw [norm_smul, Real.norm_of_nonneg (Grad.AxisSplit.axisWeight_pos parameters grade cell).le, mul_pow]
    rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem axisToTangent_norm (grade : ℕ) (family : TCore parameters) :
    tangentNorm grade (axisToTangent parameters family) = axisGradeNorm parameters grade family := by
  rw [← tangentToGrade_norm]
  apply congrArg norm
  apply lp.ext
  funext cell
  change (Grad.AxisCore.axisWeight parameters grade cell : ℂ) • family.val cell =
    Grad.AxisSplit.axisWeight parameters grade cell • family.val cell
  rw [Complex.coe_smul]
  rfl

def RealAxisData (data : AxisData parameters) : Prop :=
  (∀ cell index, data.1.val (-cell) index = conj (data.1.val cell index)) ∧
    (∀ cell index, data.2.val (-cell) index = conj (data.2.val cell index))

def axisDataCapLift (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (data : AxisData parameters) (real : RealAxisData data) : stateSmoothRange parameters reference insideR :=
  referenceCapLift parameters radius positive bounded reference insideR seed insideS base axis
    (axisToTangent parameters data.1) (axisToTangent parameters data.2) real.1 real.2

theorem chartKappa_axisDataCapLift (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (data : AxisData parameters) (real : RealAxisData data) :
    chartKappa parameters reference insideR
      (axisDataCapLift parameters radius positive bounded reference insideR seed insideS base axis data real) =
      (data.1.val, data.2.val) :=
  chartKappa_referenceCapLift radius positive bounded reference insideR seed insideS base axis
    (axisToTangent parameters data.1) (axisToTangent parameters data.2) real.1 real.2

theorem capScalarAffine_value_factor (radius : ℝ) (positive : 0 < radius)
    (sigma : TangentCoefficient parameters) (cell : ℤ) (point : ClosedDisk) :
    ((capScalarAffine parameters radius positive sigma).val cell).value point =
      (radialCap radius positive point.val : ℂ) •
        (((tameScalarMultiplier 1 (tangentComponent sigma 0) (tameCoordinateScalarField parameters 0) +
          tameScalarMultiplier 1 (tangentComponent sigma 1) (tameCoordinateScalarField parameters 1)).val cell).value point) := by
  rw [capScalarAffine, acore_val_add, closedJet_value_add, acore_val_add, closedJet_value_add]
  have law (coordinate : Fin 2) := tameScalarMultiplier_value_factor (tangentComponent sigma coordinate)
    (capScalarCoordinate parameters radius positive coordinate) (tameCoordinateScalarField parameters coordinate)
    point (radialCap radius positive point.val : ℂ)
    (fun index => capCoordinateCore_value_factor parameters radius positive coordinate _ index point) cell
  change ((tameScalarMultiplier 1 (tangentComponent sigma 0) (capScalarCoordinate parameters radius positive 0)).val cell).value point +
      ((tameScalarMultiplier 1 (tangentComponent sigma 1) (capScalarCoordinate parameters radius positive 1)).val cell).value point =
    (radialCap radius positive point.val : ℂ) •
      (((tameScalarMultiplier 1 (tangentComponent sigma 0) (tameCoordinateScalarField parameters 0)).val cell).value point +
        ((tameScalarMultiplier 1 (tangentComponent sigma 1) (tameCoordinateScalarField parameters 1)).val cell).value point)
  rw [law 0, law 1, smul_add]

theorem capScalarAffine_zero_outside (radius : ℝ) (positive : 0 < radius)
    (sigma : TangentCoefficient parameters) (cell : ℤ) (point : ClosedDisk)
    (outside : radius / 2 ≤ ‖point.val‖) :
    ((capScalarAffine parameters radius positive sigma).val cell).value point = 0 := by
  rw [capScalarAffine_value_factor, radialCap_zero radius positive point.val outside,
    Complex.ofReal_zero, zero_smul]

end Grad.ChartAxisLift
