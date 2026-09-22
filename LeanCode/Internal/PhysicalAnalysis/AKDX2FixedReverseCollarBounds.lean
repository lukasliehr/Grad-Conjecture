import AKDX1FixedInverseChartBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter
open scoped BigOperators ContDiff Topology
namespace Grad.OriginalCollarNorm
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift

theorem reverseCollar_axis_derivative_bound {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field)
    (lower : ℝ) (positive : 0<lower) (grade order : ℕ) (upper : order ≤ grade) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    ‖iteratedFDeriv ℝ order field (collarAxis radius)‖ ≤
      order.factorial * polarJetEnvelope (field ∘ collarPlane) grade (1 - radius, 0) *
        inverseChartBound lower positive grade ^ order := by
  have radiusPositive : 0 < radius := positive.trans_le inside.1
  have chartMember : collarAxis radius ∈ rightHalfPlane := radiusPositive
  have inverseSmooth : ContDiffOn ℝ ∞ inverseCollarChart rightHalfPlane :=
    fun point pointIn => (inverseCollarChart_smoothAt point pointIn).contDiffWithinAt
  have outerBounds : ∀ index, index ≤ order →
      ‖iteratedFDerivWithin ℝ index (field ∘ collarPlane) univ
        (inverseCollarChart (collarAxis radius))‖ ≤
          polarJetEnvelope (field ∘ collarPlane) grade (1 - radius, 0) := by
    intro index indexBound
    rw [iteratedFDerivWithin_univ, inverseCollarChart_axis radius radiusPositive]
    exact polarJetEnvelope_bound _ grade index (indexBound.trans upper) _
  have innerBounds : ∀ index, 1 ≤ index → index ≤ order →
      ‖iteratedFDerivWithin ℝ index inverseCollarChart rightHalfPlane (collarAxis radius)‖ ≤
        inverseChartBound lower positive grade ^ index := by
    intro index indexPositive indexBound
    rw [iteratedFDerivWithin_of_isOpen index rightHalfPlane_open chartMember]
    apply (inverseChart_derivative_bound lower positive grade index (indexBound.trans upper) radius inside).trans
    simpa only [pow_one] using pow_le_pow_right₀ (inverseChartBound_one_le lower positive grade) indexPositive
  have composite := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := order) (N := ∞)
    (s := rightHalfPlane) (t := univ) (smooth.comp collarPlane_smooth).contDiffOn inverseSmooth
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤)) uniqueDiffOn_univ
    rightHalfPlane_open.uniqueDiffOn (mapsTo_univ _ _) chartMember outerBounds innerBounds
  rw [iteratedFDerivWithin_of_isOpen order rightHalfPlane_open chartMember] at composite
  have agreement : ((field ∘ collarPlane) ∘ inverseCollarChart) =ᶠ[𝓝 (collarAxis radius)] field := by
    filter_upwards [rightHalfPlane_open.mem_nhds chartMember] with point pointIn
    change field (collarPlane (inverseCollarChart point)) = field point
    rw [collarPlane_inverseCollarChart point pointIn]
  rw [(agreement.iteratedFDeriv (𝕜 := ℝ) order).eq_of_nhds] at composite
  exact composite

open Grad.GaugeCoefficients.Radial Grad.DiskExtension.Operator

theorem reverseCollar_derivative_bound {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field)
    (lower : ℝ) (positive : 0<lower) (grade order : ℕ) (upper : order ≤ grade) (point : ℝ × ℝ)
    (inside : point.1 ∈ Icc (0 : ℝ) (1-lower)) :
    ‖iteratedFDeriv ℝ order field (collarPlane point)‖ ≤
      order.factorial * inverseChartBound lower positive grade ^ order *
        polarJetEnvelope (field ∘ collarPlane) grade point := by
  have radiusIn : 1 - point.1 ∈ Icc lower 1 := by
    constructor <;> linarith [inside.1, inside.2]
  have rotatedSmooth : ContDiff ℝ ∞ (field ∘ planeRotationEquiv point.2) :=
    smooth.comp (planeRotationEquiv point.2).contDiff
  have estimate := reverseCollar_axis_derivative_bound (field ∘ planeRotationEquiv point.2)
    rotatedSmooth lower positive grade order upper (1 - point.1) radiusIn
  rw [(planeRotationEquiv point.2).norm_iteratedFDeriv_comp_right field,
    planeRotation_axis, sub_sub_cancel, polarJetEnvelope_rotation] at estimate
  have pointEquality : (point.1, (0 : ℝ)) + (0, point.2) = point := by ext <;> simp
  rw [pointEquality] at estimate
  apply estimate.trans_eq
  ring

theorem reverseCollar_derivative_sq_bound {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field)
    (lower : ℝ) (positive : 0<lower) (grade order : ℕ) (upper : order ≤ grade) (point : ℝ × ℝ)
    (inside : point.1 ∈ Icc (0 : ℝ) (1-lower)) :
    ‖iteratedFDeriv ℝ order field (collarPlane point)‖ ^ 2 ≤
      ((order.factorial * inverseChartBound lower positive grade ^ order) ^ 2 * (grade + 1 : ℝ)) *
        polarJetSquaredDensity (field ∘ collarPlane) grade point := by
  calc
    _ ≤ (order.factorial * inverseChartBound lower positive grade ^ order *
          polarJetEnvelope (field ∘ collarPlane) grade point) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (reverseCollar_derivative_bound field smooth lower positive grade order upper point inside) 2
    _ = (order.factorial * inverseChartBound lower positive grade ^ order) ^ 2 *
        polarJetEnvelope (field ∘ collarPlane) grade point ^ 2 := mul_pow _ _ _
    _ ≤ (order.factorial * inverseChartBound lower positive grade ^ order) ^ 2 *
        ((grade + 1 : ℝ) * polarJetSquaredDensity (field ∘ collarPlane) grade point) :=
      mul_le_mul_of_nonneg_left (polarJetEnvelope_sq_le _ grade point) (sq_nonneg _)
    _ = _ := by ring

end Grad.OriginalCollarNorm
