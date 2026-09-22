import ARC2HalfReverseCollar

noncomputable section
open Set
open scoped BigOperators ContDiff
namespace Grad.CollarCartesian
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift
open Grad.GaugeCoefficients.Radial Grad.DiskExtension.Operator

theorem reverseCollar_derivative_bound {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field)
    (grade order : ℕ) (upper : order ≤ grade) (point : ℝ × ℝ)
    (inside : point.1 ∈ Icc (0 : ℝ) (1 / 2)) :
    ‖iteratedFDeriv ℝ order field (collarPlane point)‖ ≤
      order.factorial * inverseChartBound grade ^ order *
        polarJetEnvelope (field ∘ collarPlane) grade point := by
  have radiusIn : 1 - point.1 ∈ Icc (1 / 2 : ℝ) 1 := by
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

theorem reverseCollar_derivative_sq_bound {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field)
    (grade order : ℕ) (upper : order ≤ grade) (point : ℝ × ℝ)
    (inside : point.1 ∈ Icc (0 : ℝ) (1 / 2)) :
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

end Grad.CollarCartesian
