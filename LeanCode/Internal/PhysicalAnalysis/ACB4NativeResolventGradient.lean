import ACB2RadialVolterraGradient
import ACB3VolterraNativeValueBound

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.ActualCenterVolterra
open Grad.NonlinearDivision (IsRotationInvariant)

theorem coordinate_value_norm {dimension : ℕ} (direction : Fin 2) (field : ClosedJet dimension) :
    ‖(coordinateJet direction field).value‖ ≤ ‖field.value‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro point
  rw [coordinateJet_value, norm_smul]
  have small : ‖point.val direction‖ ≤ 1 := (PiLp.norm_apply_le point.val direction).trans point.property
  exact (mul_le_of_le_one_left (norm_nonneg _) small).trans (ContinuousMap.norm_coe_le_norm _ _)

theorem radial_add_smul {dimension : ℕ} (first second : ClosedJet dimension) (scalar : ℂ)
    (firstRadial : IsRotationInvariant first) (secondRadial : IsRotationInvariant second) :
    IsRotationInvariant (first + scalar • second) := by
  intro angle point
  simp only [closedJet_value_add, closedJet_value_smul, ContinuousMap.add_apply,
    ContinuousMap.smul_apply, firstRadial angle point, secondRadial angle point]

theorem volterraResolvent_integral_equation {dimension : ℕ} (parameter : ℝ)
    (field : ClosedJet dimension) (radial : IsRotationInvariant field) :
    volterraResolventJet parameter field =
      volterraJet (field + (parameter : ℂ) • volterraResolventJet parameter field) := by
  apply pinnedRadial_volterra_inverse 1 (Or.inl rfl) _ _
    (volterraResolvent_radial parameter field radial) (volterraResolvent_origin parameter field)
  rw [volterraResolvent_equation 1 (Or.inl rfl) parameter field radial]
  simp only [centerCoordinate_decomposition, centerCoordinate_add, centerCoordinate_smul]
  module

def centerGradientConstant (radius : ℝ) : ℝ :=
  (1 + 3 * radius ^ 2 * centerValueConstant radius) / 4

theorem centerGradientConstant_nonnegative (radius : ℝ) : 0 ≤ centerGradientConstant radius := by
  have value := centerValueConstant_nonnegative radius
  unfold centerGradientConstant
  positivity

/-- The exact resolvent has a first derivative bound paid entirely by the
C0 forcing. No derivative of the quotient source appears. -/
theorem volterraResolvent_partial_norm {dimension : ℕ} (radius parameter : ℝ)
    (bounded : |parameter| ≤ 3 * radius ^ 2) (field : ClosedJet dimension)
    (radial : IsRotationInvariant field) (direction : Fin 2) :
    ‖(partialJet direction (volterraResolventJet parameter field)).value‖ ≤
      centerGradientConstant radius * ‖field.value‖ := by
  let result := volterraResolventJet parameter field
  have identity : partialJet direction result =
      coordinateJet direction (powerDilationJet 3 (field + (parameter : ℂ) • result)) := by
    conv_lhs => rw [show result = volterraJet (field + (parameter : ℂ) • result) from
      volterraResolvent_integral_equation parameter field radial]
    exact partial_volterra_radial direction _ (radial_add_smul field result _ radial
      (volterraResolvent_radial parameter field radial))
  rw [identity]
  have integral := powerDilationJet_derivative_norm 3 (field + (parameter : ℂ) • result) emptyCartesianWord
  simp only [closedDerivative_zero_order, Nat.cast_zero, Nat.cast_ofNat, add_zero] at integral
  have forcing : ‖(field + (parameter : ℂ) • result).value‖ ≤
      (1 + 3 * radius ^ 2 * centerValueConstant radius) * ‖field.value‖ := by
    rw [closedJet_value_add, closedJet_value_smul]
    calc
      _ ≤ ‖field.value‖ + ‖(parameter : ℂ) • result.value‖ := norm_add_le _ _
      _ = ‖field.value‖ + |parameter| * ‖result.value‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖field.value‖ + (3 * radius ^ 2) * (centerValueConstant radius * ‖field.value‖) :=
        add_le_add le_rfl (mul_le_mul bounded (volterraResolvent_value_norm radius parameter bounded field)
          (norm_nonneg _) (by positivity))
      _ = _ := by ring
  exact (coordinate_value_norm direction _).trans (integral.trans
    ((div_le_div_of_nonneg_right forcing (by norm_num)).trans_eq (by unfold centerGradientConstant; ring)))

end Grad.ActualCenterBounds
