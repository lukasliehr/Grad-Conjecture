import ARC6HalfCollarIntegral

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CollarCartesian
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift

def halfReverseConstant (order : ℕ) : ℝ :=
  (order.factorial * inverseChartBound order ^ order) ^ 2 * (order + 1 : ℝ)

theorem halfReverseConstant_nonnegative (order : ℕ) : 0 ≤ halfReverseConstant order := by
  unfold halfReverseConstant
  positivity

theorem derivative_zero_inner {dimension : ℕ} (field : SpatialPlane → ComplexEuclidean dimension)
    (vanishes : ∀ point, ‖point‖ < (7 / 12 : ℝ) → field point = 0)
    (order : ℕ) (point : SpatialPlane) (inside : ‖point‖ ≤ (1 / 2 : ℝ)) :
    iteratedFDeriv ℝ order field point = 0 := by
  have pointIn : point ∈ Metric.ball (0 : SpatialPlane) (7 / 12 : ℝ) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have agreement : field =ᶠ[𝓝 point] (0 : SpatialPlane → ComplexEuclidean dimension) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds pointIn] with source sourceIn
    apply vanishes
    simpa only [Metric.mem_ball, dist_zero_right] using sourceIn
  simpa only [iteratedFDeriv_zero, Pi.zero_apply] using
    (agreement.iteratedFDeriv (𝕜 := ℝ) order).eq_of_nhds

theorem cartesian_tensor_halfCollar_energy {dimension : ℕ}
    (field : SpatialPlane → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (vanishes : ∀ point, ‖point‖ < (7 / 12 : ℝ) → field point = 0) (order : ℕ) :
    (∫ point in closedUnitDisk, ‖iteratedFDeriv ℝ order field point‖ ^ 2) ≤
      halfReverseConstant order *
        halfCollarIntegral (polarJetSquaredDensity (field ∘ collarPlane) order) := by
  have tensorContinuous : Continuous (fun point => ‖iteratedFDeriv ℝ order field point‖ ^ 2) :=
    ((smooth.continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm).pow 2
  have diskBound := disk_integral_le_halfCollar _ tensorContinuous (fun _ => sq_nonneg _) (by
    intro point inside
    rw [derivative_zero_inner field vanishes order point inside, norm_zero, zero_pow (by norm_num)])
  have comparison := halfCollarIntegral_mono
    (fun point => ‖iteratedFDeriv ℝ order field (collarPlane point)‖ ^ 2)
    (fun point => halfReverseConstant order * polarJetSquaredDensity (field ∘ collarPlane) order point)
    (tensorContinuous.comp collarPlane_smooth.continuous)
    (continuous_const.mul (polarJetSquaredDensity_continuous _ (smooth.comp collarPlane_smooth) order))
    (by intro point inside; exact reverseCollar_derivative_sq_bound field smooth order order le_rfl point inside.1)
  rw [halfCollarIntegral_const_mul] at comparison
  exact diskBound.trans comparison

/-- Literal Cartesian derivative L2 row with the original disk-area measure. -/
theorem closedDerivative_halfCollar_energy {dimension : ℕ}
    (field : SpatialPlane → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (vanishes : ∀ point, ‖point‖ < (7 / 12 : ℝ) → field point = 0)
    (index : CartesianMultiIndex) :
    ‖closedDerivativeL2 index (globalClosedJet field smooth)‖ ^ 2 ≤
      halfReverseConstant (cartesianOrder index) * halfCollarIntegral
        (polarJetSquaredDensity (field ∘ collarPlane) (cartesianOrder index)) :=
  (globalClosedDerivative_energy_bound field smooth index).trans
    (cartesian_tensor_halfCollar_energy field smooth vanishes (cartesianOrder index))

end Grad.CollarCartesian
