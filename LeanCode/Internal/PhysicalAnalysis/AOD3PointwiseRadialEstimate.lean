import AOD2ReciprocalBounds

noncomputable section
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff BigOperators
namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.AnnularSourceGraph Grad.SourceCollarDivision

def radialProductConstant (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (order : ℕ) : ℝ :=
  ((order + 1 : ℕ) : ℝ) * reciprocalJetBound lower positive bounded order ^ 2

theorem radialProductConstant_nonnegative (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (order : ℕ) :
    0 ≤ radialProductConstant lower positive bounded order := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

private theorem norm_radial_quad_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (first second value forcing : E) (mode scalar : ℝ) :
    ‖-first + mode ^ 2 • second + scalar • value - forcing‖ ^ 2 ≤
      4 * (‖first‖ ^ 2 + mode ^ 4 * ‖second‖ ^ 2 + scalar ^ 2 * ‖value‖ ^ 2 + ‖forcing‖ ^ 2) := by
  have raw := norm_four_sq (-first) (mode ^ 2 • second) (scalar • value) (-forcing)
  simpa only [sub_eq_add_neg, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← pow_mul] using raw

private theorem boundedMultiplier_square (parameter ceiling multiplier : ℝ)
    (parameterBound : |parameter| ≤ ceiling) (nonnegative : 0 ≤ multiplier) (upper : multiplier ≤ 1) :
    (parameter ^ 2 * multiplier) ^ 2 ≤ ceiling ^ 4 := by
  have parameterSquare : parameter ^ 2 ≤ ceiling ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg parameter) parameterBound 2
  have product : parameter ^ 2 * multiplier ≤ ceiling ^ 2 :=
    (mul_le_mul_of_nonneg_left upper (sq_nonneg parameter)).trans (by simpa only [mul_one] using parameterSquare)
  exact (pow_le_pow_left₀ (mul_nonneg (sq_nonneg parameter) nonnegative) product 2).trans_eq (by ring)

/-- Every radial count is bounded by lower genuine radial counts, at the
same or smaller total differential order, and the actual source derivative. -/
theorem actualRadial_jet_pointwise (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter ceiling : ℝ) (parameterBound : |parameter| ≤ ceiling)
    (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (mode : ℤ) (high : mode ∉ lowAngularModes) (order : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    ‖iteratedDerivWithin (order + 2) (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1) radius‖ ^ 2 ≤
      4 * (radialProductConstant lower positive bounded order *
        (∑ index ∈ Finset.range (order + 1),
          ‖iteratedDerivWithin (order - index + 1) (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1) radius‖ ^ 2) +
        (mode : ℝ) ^ 4 * radialProductConstant lower positive bounded order *
        (∑ index ∈ Finset.range (order + 1),
          ‖iteratedDerivWithin (order - index) (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1) radius‖ ^ 2) +
        ceiling ^ 4 * ‖iteratedDerivWithin order (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1) radius‖ ^ 2 +
        ‖iteratedDerivWithin order (diskCoreRadialCurve mode core) (Icc lower 1) radius‖ ^ 2) := by
  let value : ℝ → ComplexEuclidean 1 := actualRadialValue lower positive bounded mode parameter source
  let first := radialLeibniz order (fun radius : ℝ => radius⁻¹) (derivWithin value (Icc lower 1)) (Icc lower 1) radius
  let second := radialLeibniz order (fun radius : ℝ => radius⁻¹ ^ 2) value (Icc lower 1) radius
  have firstBound : ‖first‖ ^ 2 ≤ radialProductConstant lower positive bounded order *
      ∑ index ∈ Finset.range (order + 1), ‖iteratedDerivWithin (order - index + 1) value (Icc lower 1) radius‖ ^ 2 := by
    have bound := radialLeibniz_norm_sq order (fun radius : ℝ => radius⁻¹)
      (derivWithin value (Icc lower 1)) (Icc lower 1) radius (reciprocalJetBound lower positive bounded order)
      (fun index upper => (reciprocalJet_bound lower positive bounded order index upper radius inside).1)
    simpa only [first, radialProductConstant, iteratedDerivWithin_succ'] using bound
  have secondBound : ‖second‖ ^ 2 ≤ radialProductConstant lower positive bounded order *
      ∑ index ∈ Finset.range (order + 1), ‖iteratedDerivWithin (order - index) value (Icc lower 1) radius‖ ^ 2 :=
    radialLeibniz_norm_sq order (fun radius : ℝ => radius⁻¹ ^ 2) value (Icc lower 1) radius
      (reciprocalJetBound lower positive bounded order)
      (fun index upper => (reciprocalJet_bound lower positive bounded order index upper radius inside).2)
  have actual := norm_radial_quad_sq first second (iteratedDerivWithin order value (Icc lower 1) radius)
    (iteratedDerivWithin order (diskCoreRadialCurve mode core) (Icc lower 1) radius)
    (mode : ℝ) (parameter ^ 2 * highMultiplier mode)
  have scalarBound := mul_le_mul_of_nonneg_right
    (boundedMultiplier_square parameter ceiling (highMultiplier mode) parameterBound
      (highMultiplier_nonnegative mode) (highMultiplier_one_le mode))
    (sq_nonneg ‖iteratedDerivWithin order value (Icc lower 1) radius‖)
  have bound := actual.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add firstBound
      (mul_le_mul_of_nonneg_left secondBound (by positivity : 0 ≤ (mode : ℝ) ^ 4))) scalarBound) le_rfl)
    (by norm_num : (0 : ℝ) ≤ 4))
  have equation := congrArg (fun derivative : ComplexEuclidean 1 => ‖derivative‖ ^ 2)
    (actualRadial_differentiated_equation lower positive bounded parameter source core same mode high order radius inside)
  exact equation.trans_le (bound.trans_eq (by simp only [value, mul_assoc]))

end Grad.CircularHighRegularity
