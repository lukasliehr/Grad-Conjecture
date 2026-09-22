import AKDX3FixedCollarIntegral
import ARC11LocalCutoffCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.OriginalCollarNorm
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift
open Grad.DiskExtension.Operator

def fixedCollarRectangle (lower : ℝ) : Set (ℝ × ℝ) := Icc (0:ℝ) (1-lower) ×ˢ Icc (-Real.pi) Real.pi

theorem fixedCollarIntegral_mono (lower : ℝ) (bounded : lower<1) (first second : ℝ × ℝ → ℝ)
    (firstContinuous : Continuous first) (secondContinuous : Continuous second)
    (bound : ∀ point ∈ fixedCollarRectangle lower, first point ≤ second point) :
    fixedCollarIntegral lower first ≤ fixedCollarIntegral lower second := by
  apply integral_mono_ae
  · exact ((timeIntegral_continuous first firstContinuous 0 (1-lower) (by linarith)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · exact ((timeIntegral_continuous second secondContinuous 0 (1-lower) (by linarith)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with angle angleIn
    apply intervalIntegral.integral_mono_on (by linarith : (0 : ℝ) ≤ 1-lower)
    · exact (firstContinuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    · exact (secondContinuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    · intro time timeIn
      exact bound (time, angle) ⟨timeIn, ⟨angleIn.1.le, angleIn.2.le⟩⟩

theorem fixedCollarIntegral_const_mul (lower : ℝ) (scalar : ℝ) (function : ℝ × ℝ → ℝ) :
    fixedCollarIntegral lower (fun point => scalar * function point) = scalar * fixedCollarIntegral lower function := by
  unfold fixedCollarIntegral
  simp only [intervalIntegral.integral_const_mul, integral_const_mul]

def fixedReverseConstant (lower : ℝ) (positive : 0<lower) (order : ℕ) : ℝ :=
  (order.factorial*inverseChartBound lower positive order^order)^2*(order+1:ℝ)

theorem fixedReverseConstant_nonnegative (lower : ℝ) (positive : 0<lower) (order : ℕ) :
    0≤fixedReverseConstant lower positive order := by unfold fixedReverseConstant; positivity

theorem derivative_zero_inner {dimension : ℕ} (lower : ℝ) (positive : 0<lower) (field : SpatialPlane → ComplexEuclidean dimension)
    (vanishes : ∀ point, ‖point‖ < (2*lower) → field point = 0)
    (order : ℕ) (point : SpatialPlane) (inside : ‖point‖ ≤ lower) :
    iteratedFDeriv ℝ order field point = 0 := by
  have pointIn : point ∈ Metric.ball (0 : SpatialPlane) (2*lower) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have agreement : field =ᶠ[𝓝 point] (0 : SpatialPlane → ComplexEuclidean dimension) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds pointIn] with source sourceIn
    apply vanishes
    simpa only [Metric.mem_ball, dist_zero_right] using sourceIn
  simpa only [iteratedFDeriv_zero, Pi.zero_apply] using
    (agreement.iteratedFDeriv (𝕜 := ℝ) order).eq_of_nhds

theorem cartesian_tensor_fixedCollar_energy {dimension : ℕ} (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (field : SpatialPlane → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (vanishes : ∀ point, ‖point‖ < (2*lower) → field point = 0) (order : ℕ) :
    (∫ point in closedUnitDisk, ‖iteratedFDeriv ℝ order field point‖ ^ 2) ≤
      fixedReverseConstant lower positive order *
        fixedCollarIntegral lower (polarJetSquaredDensity (field ∘ collarPlane) order) := by
  have tensorContinuous : Continuous (fun point => ‖iteratedFDeriv ℝ order field point‖ ^ 2) :=
    ((smooth.continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm).pow 2
  have diskBound := disk_integral_le_fixedCollar lower positive bounded _ tensorContinuous (fun _ => sq_nonneg _) (by
    intro point inside
    rw [derivative_zero_inner lower positive field vanishes order point inside, norm_zero, zero_pow (by norm_num)])
  have comparison := fixedCollarIntegral_mono lower bounded
    (fun point => ‖iteratedFDeriv ℝ order field (collarPlane point)‖ ^ 2)
    (fun point => fixedReverseConstant lower positive order * polarJetSquaredDensity (field ∘ collarPlane) order point)
    (tensorContinuous.comp collarPlane_smooth.continuous)
    (continuous_const.mul (polarJetSquaredDensity_continuous _ (smooth.comp collarPlane_smooth) order))
    (by intro point inside; exact reverseCollar_derivative_sq_bound field smooth lower positive order order le_rfl point inside.1)
  rw [fixedCollarIntegral_const_mul] at comparison
  exact diskBound.trans comparison

/-- Literal Cartesian derivative L2 row with the original disk-area measure. -/
theorem closedDerivative_fixedCollar_energy {dimension : ℕ} (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (field : SpatialPlane → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (vanishes : ∀ point, ‖point‖ < (2*lower) → field point = 0)
    (index : CartesianMultiIndex) :
    ‖closedDerivativeL2 index (globalClosedJet field smooth)‖ ^ 2 ≤
      fixedReverseConstant lower positive (cartesianOrder index) * fixedCollarIntegral lower
        (polarJetSquaredDensity (field ∘ collarPlane) (cartesianOrder index)) :=
  (globalClosedDerivative_energy_bound field smooth index).trans
    (cartesian_tensor_fixedCollar_energy lower positive bounded field smooth vanishes (cartesianOrder index))

end Grad.OriginalCollarNorm
