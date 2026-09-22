import BL10ReverseCollar

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints
open Grad.GaugeCoefficients.Radial Grad.DiskExtension.Operator

theorem planeRotation_collar (angle : ℝ) (point : ℝ × ℝ) :
    planeRotationEquiv angle (collarPlane point) = collarPlane (point + (0, angle)) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [planeRotationEquiv_apply, planeRotation, collarPlane, Real.cos_add, Real.sin_add] <;> ring

theorem planeRotation_axis (angle radius : ℝ) :
    planeRotationEquiv angle (collarAxis radius) = collarPlane (1 - radius, angle) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [planeRotationEquiv_apply, planeRotation, collarAxis, collarPlane] <;> ring

theorem polarJetEnvelope_rotation {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (field : SpatialPlane → Value) (angle : ℝ) (grade : ℕ) (point : ℝ × ℝ) :
    polarJetEnvelope ((field ∘ planeRotationEquiv angle) ∘ collarPlane) grade point =
      polarJetEnvelope (field ∘ collarPlane) grade (point + (0, angle)) := by
  have representation : ((field ∘ planeRotationEquiv angle) ∘ collarPlane) =
      fun source => (field ∘ collarPlane) (source + (0, angle)) := by
    funext source
    simp only [Function.comp_apply, planeRotation_collar]
  rw [representation]
  unfold polarJetEnvelope
  simp only [iteratedFDeriv_comp_add_right]

theorem reverseCollar_derivative_bound {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field)
    (grade order : ℕ) (upper : order ≤ grade) (point : ℝ × ℝ)
    (inside : point.1 ∈ Icc (0 : ℝ) (1 / 4)) :
    ‖iteratedFDeriv ℝ order field (collarPlane point)‖ ≤
      order.factorial * inverseChartBound grade ^ order *
        polarJetEnvelope (field ∘ collarPlane) grade point := by
  have radiusIn : 1 - point.1 ∈ Icc (3 / 4 : ℝ) 1 := by
    constructor <;> linarith [inside.1, inside.2]
  have rotatedSmooth : ContDiff ℝ ∞ (field ∘ planeRotationEquiv point.2) :=
    smooth.comp (planeRotationEquiv point.2).contDiff
  have estimate := reverseCollar_axis_derivative_bound (field ∘ planeRotationEquiv point.2)
    rotatedSmooth grade order upper (1 - point.1) radiusIn
  rw [(planeRotationEquiv point.2).norm_iteratedFDeriv_comp_right field,
    planeRotation_axis, sub_sub_cancel, polarJetEnvelope_rotation] at estimate
  have pointEquality : (point.1, (0 : ℝ)) + (0, point.2) = point := by ext <;> simp
  rw [pointEquality] at estimate
  apply estimate.trans_eq
  ring

def polarJetSquaredDensity {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : ℝ × ℝ → Value) (grade : ℕ) (point : ℝ × ℝ) : ℝ :=
  ∑ order ∈ Finset.range (grade + 1), ‖iteratedFDeriv ℝ order field point‖ ^ 2

theorem polarJetEnvelope_sq_le {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : ℝ × ℝ → Value) (grade : ℕ) (point : ℝ × ℝ) :
    polarJetEnvelope field grade point ^ 2 ≤ (grade + 1 : ℝ) * polarJetSquaredDensity field grade point := by
  have cauchy := weighted_cauchy_finset (Finset.range (grade + 1)) (fun _ => (1 : ℝ))
    (fun order => ‖iteratedFDeriv ℝ order field point‖) (by intros; norm_num)
  simpa [polarJetEnvelope, polarJetSquaredDensity] using cauchy

theorem reverseCollar_derivative_sq_bound {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field)
    (grade order : ℕ) (upper : order ≤ grade) (point : ℝ × ℝ)
    (inside : point.1 ∈ Icc (0 : ℝ) (1 / 4)) :
    ‖iteratedFDeriv ℝ order field (collarPlane point)‖ ^ 2 ≤
      ((order.factorial * inverseChartBound grade ^ order) ^ 2 * (grade + 1 : ℝ)) *
        polarJetSquaredDensity (field ∘ collarPlane) grade point := by
  calc
    _ ≤ (order.factorial * inverseChartBound grade ^ order *
          polarJetEnvelope (field ∘ collarPlane) grade point) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (reverseCollar_derivative_bound field smooth grade order upper point inside) 2
    _ = (order.factorial * inverseChartBound grade ^ order) ^ 2 *
        polarJetEnvelope (field ∘ collarPlane) grade point ^ 2 := mul_pow _ _ _
    _ ≤ (order.factorial * inverseChartBound grade ^ order) ^ 2 *
        ((grade + 1 : ℝ) * polarJetSquaredDensity (field ∘ collarPlane) grade point) :=
      mul_le_mul_of_nonneg_left (polarJetEnvelope_sq_le _ grade point) (sq_nonneg _)
    _ = _ := by ring

end Grad.BoundaryLift
