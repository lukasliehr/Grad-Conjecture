import AXC8ExtractionGoal

noncomputable section

open scoped ContDiff

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds

/-- A one-variable bump composed with squared radius. A general planar
ContDiffBump need only be symmetric, which is insufficient for AL17. -/
def radialCapBase (radius : ℝ) (positive : 0 < radius) : ContDiffBump (0 : ℝ) :=
  ⟨(radius / 4) ^ 2, (radius / 2) ^ 2, by positivity, by nlinarith [sq_pos_of_pos positive]⟩

def radialCap (radius : ℝ) (positive : 0 < radius) (point : SpatialPlane) : ℝ :=
  radialCapBase radius positive (‖point‖ ^ 2)

theorem radialCap_smooth (radius : ℝ) (positive : 0 < radius) :
    ContDiff ℝ ∞ (radialCap radius positive) :=
  (radialCapBase radius positive).contDiff.comp (contDiff_norm_sq ℝ)

theorem radialCap_one (radius : ℝ) (positive : 0 < radius) (point : SpatialPlane)
    (inside : ‖point‖ ≤ radius / 4) : radialCap radius positive point = 1 := by
  apply (radialCapBase radius positive).one_of_mem_closedBall
  change dist (‖point‖ ^ 2) 0 ≤ (radius / 4) ^ 2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) inside 2

theorem radialCap_zero (radius : ℝ) (positive : 0 < radius) (point : SpatialPlane)
    (outside : radius / 2 ≤ ‖point‖) : radialCap radius positive point = 0 := by
  apply (radialCapBase radius positive).zero_of_le_dist
  change (radius / 2) ^ 2 ≤ dist (‖point‖ ^ 2) 0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (by positivity) outside 2

theorem radialCap_origin (radius : ℝ) (positive : 0 < radius) :
    radialCap radius positive (0 : SpatialPlane) = 1 :=
  radialCap_one radius positive 0 (by simpa only [norm_zero] using (show 0 ≤ radius / 4 by positivity))

theorem radialCap_isometry (radius : ℝ) (positive : 0 < radius)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (point : SpatialPlane) :
    radialCap radius positive (orthogonal point) = radialCap radius positive point := by
  simp only [radialCap, orthogonal.norm_map]

theorem radialCap_neg (radius : ℝ) (positive : 0 < radius) (point : SpatialPlane) :
    radialCap radius positive (-point) = radialCap radius positive point := by
  simp only [radialCap, norm_neg]

def radialCapLinearField {dimension : ℕ} (radius : ℝ) (positive : 0 < radius)
    (coordinate : Fin 2) (vector : ComplexEuclidean dimension) : SpatialPlane → ComplexEuclidean dimension :=
  fun point => (radialCap radius positive point * coordinateLinear coordinate point) • vector

theorem radialCapLinearField_smooth {dimension : ℕ} (radius : ℝ) (positive : 0 < radius)
    (coordinate : Fin 2) (vector : ComplexEuclidean dimension) :
    ContDiff ℝ ∞ (radialCapLinearField radius positive coordinate vector) :=
  ((radialCap_smooth radius positive).mul (coordinateLinear coordinate).contDiff).smul contDiff_const

def radialCapJet {dimension : ℕ} (radius : ℝ) (positive : 0 < radius)
    (coordinate : Fin 2) (vector : ComplexEuclidean dimension) : ClosedJet dimension :=
  globalClosedJet (radialCapLinearField radius positive coordinate vector)
    (radialCapLinearField_smooth radius positive coordinate vector)

theorem radialCapJet_originValue {dimension : ℕ} (radius : ℝ) (positive : 0 < radius)
    (coordinate : Fin 2) (vector : ComplexEuclidean dimension) :
    originValue (radialCapJet radius positive coordinate vector) = 0 := by
  rw [originValue, radialCapJet, globalClosedJet_value]
  change (radialCap radius positive 0 * 0) • vector = 0
  rw [mul_zero, zero_smul]

theorem radialCapJet_originPartial {dimension : ℕ} (radius : ℝ) (positive : 0 < radius)
    (direction coordinate : Fin 2) (vector : ComplexEuclidean dimension) :
    originPartial direction (radialCapJet radius positive coordinate vector) =
      if direction = coordinate then vector else 0 := by
  rw [originPartial_eq_closedDerivative, radialCapJet, globalClosedJet_derivative,
    ← spatialPartial_eq_ordered]
  change fderiv ℝ (fun point : SpatialPlane =>
    (radialCap radius positive point * coordinateLinear coordinate point) • vector) 0 (spatialBasis direction) = _
  have scalarDiff := (((radialCap_smooth radius positive).mul
    (coordinateLinear coordinate).contDiff).differentiable (by simp)).differentiableAt (x := (0 : SpatialPlane))
  rw [fderiv_smul_const scalarDiff vector, ContinuousLinearMap.smulRight_apply,
    fderiv_fun_mul (((radialCap_smooth radius positive).differentiable (by simp)).differentiableAt)
      ((coordinateLinear coordinate).differentiableAt)]
  rw [add_apply, smul_apply, smul_apply, radialCap_origin, (coordinateLinear coordinate).fderiv]
  change (1 * spatialBasis direction coordinate + (0 : ℝ) * _) • vector = _
  rw [zero_mul, one_mul, add_zero]
  by_cases same : direction = coordinate
  · subst coordinate
    simp [spatialBasis]
  · simp [spatialBasis, same, Ne.symm same]

end Grad.ChartAxisLift
