import TameRootCollapse

noncomputable section

set_option maxHeartbeats 1600000

open Filter
open scoped BigOperators ENNReal NNReal Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The genuine envelope derivative of the shifted root series along
quadratic curves: the total shifted series, the exact termwise remainder
decomposition, and the derivative `G_k' = G_{k+1} · u`. -/

variable {parameters : PhaseParameters}

/-- The total shifted root series: the series on the strict grade-zero
ball, zero outside. -/
def tameRootShifted (order : ℕ) (x : TameCoefficient parameters) :
    TameCoefficient parameters :=
  if small : coefficientEnvelope 0 x < 1 then rootShiftedSeries order x small else 0

theorem tameRootShifted_of_small (order : ℕ) {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) :
    tameRootShifted order x = rootShiftedSeries order x small := dif_pos small

/-- Series terms agree pointwise, so the sums agree. -/
theorem tameSeries_congr_terms {Index : Type}
    {firstTerms secondTerms : Index → TameCoefficient parameters}
    {firstMajorant secondMajorant : ℕ → Index → ℝ}
    (firstMajor : SeriesMajorant firstTerms firstMajorant)
    (secondMajor : SeriesMajorant secondTerms secondMajorant)
    (agree : ∀ index, firstTerms index = secondTerms index) :
    tameSeries firstTerms firstMajor = tameSeries secondTerms secondMajor := by
  apply Subtype.ext
  funext cell
  exact tsum_congr (fun index => by rw [agree index])

/-- The termwise remainder decomposition of the shifted-series difference
along the quadratic curve. -/
theorem rootShifted_difference_terms (order q : ℕ)
    {x : TameCoefficient parameters} (u w : TameCoefficient parameters) (t : ℝ) :
    ((rootDerivativeCoefficient order (q + 1) : ℝ) : ℂ) •
        (rootCurvePoint x u w t) ^ (q + 1) -
      ((rootDerivativeCoefficient order (q + 1) : ℝ) : ℂ) • x ^ (q + 1) -
      (t : ℂ) • (((rootDerivativeCoefficient (order + 1) q : ℝ) : ℂ) • x ^ q * u) =
    ((rootDerivativeCoefficient order (q + 1) : ℝ) : ℂ) •
      rootCurveRemainder x u w t q := by
  rw [tameSmul_mul, rootCurveRemainder, smul_sub, smul_sub]
  congr 1
  rw [smul_smul, smul_smul]
  congr 1
  rw [← rootDerivativeCoefficient_shift order q]
  push_cast
  ring

/-- The quadratic remainder majorant certificate for the difference series. -/
theorem rootRemainder_series_majorant (order : ℕ) {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (u w : TameCoefficient parameters)
    {t : ℝ} (inside : |t| ≤ rootCurveRadius x u w) :
    SeriesMajorant (fun q => ((rootDerivativeCoefficient order (q + 1) : ℝ) : ℂ) •
        rootCurveRemainder x u w t q)
      (fun grade q => |rootDerivativeCoefficient order (q + 1)| *
        (t ^ 2 * (rootQuadScale x u w grade (q + 1) * rootCollapseRatio x ^ (q + 1)))) := by
  intro grade
  constructor
  · intro q
    rw [coefficientEnvelope_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (rootCurveRemainder_envelope_le small u w grade q inside) (abs_nonneg _)
  · -- Polynomial-times-geometric summability of the static majorant.
    have ratio_pos := rootCollapseRatio_pos x
    have ratio_lt := rootCollapseRatio_lt_one small
    have radius_pos := rootCurveRadius_pos small u w
    have scale_shape : ∀ q : ℕ, rootQuadScale x u w grade (q + 1) =
        (((rootCurveRadius x u w)⁻¹) ^ 2 * (6 * 4 ^ grade *
          rootEnvelopeScale x u w grade * rootEnvelopeScale x u w 0 ^ 2)) *
          ((q + 1 + 1 : ℕ) : ℝ) ^ (grade + 1) := by
      intro q
      rw [rootQuadScale]
      ring
    have comparison : Summable (fun q : ℕ =>
        ((q + 1 + order : ℕ) : ℝ) ^ order *
          ((((rootCurveRadius x u w)⁻¹) ^ 2 * (6 * 4 ^ grade *
            rootEnvelopeScale x u w grade * rootEnvelopeScale x u w 0 ^ 2)) *
            (((q + 1 + 1 : ℕ) : ℝ) ^ (grade + 1) *
              (t ^ 2 * rootCollapseRatio x ^ (q + 1))))) := by
      have polynomial_summable : Summable (fun q : ℕ =>
          (((order + 2 : ℕ) : ℝ)) ^ (order + grade + 1) *
            (((q + 1 : ℕ) : ℝ) ^ (order + grade + 1) * rootCollapseRatio x ^ q)) :=
        Summable.mul_left _
          (summable_succ_pow_mul_geometric (order + grade + 1) ratio_pos ratio_lt)
      apply Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_)
        ((polynomial_summable.mul_left
          ((((rootCurveRadius x u w)⁻¹) ^ 2 * (6 * 4 ^ grade *
            rootEnvelopeScale x u w grade * rootEnvelopeScale x u w 0 ^ 2)) *
            (t ^ 2 * rootCollapseRatio x))))
      · have := rootEnvelopeScale_nonneg x u w grade
        have := rootEnvelopeScale_nonneg x u w 0
        positivity
      · have cast_le_one : ((q + 1 + order : ℕ) : ℝ) ^ order *
            ((q + 1 + 1 : ℕ) : ℝ) ^ (grade + 1) ≤
            (((order + 2 : ℕ) : ℝ)) ^ (order + grade + 1) *
              ((q + 1 : ℕ) : ℝ) ^ (order + grade + 1) := by
          have first_le : ((q + 1 + order : ℕ) : ℝ) ≤
              ((order + 2 : ℕ) : ℝ) * ((q + 1 : ℕ) : ℝ) := by
            push_cast
            nlinarith [Nat.cast_nonneg (α := ℝ) q, Nat.cast_nonneg (α := ℝ) order]
          have second_le : ((q + 1 + 1 : ℕ) : ℝ) ≤
              ((order + 2 : ℕ) : ℝ) * ((q + 1 : ℕ) : ℝ) := by
            push_cast
            nlinarith [Nat.cast_nonneg (α := ℝ) q, Nat.cast_nonneg (α := ℝ) order]
          calc ((q + 1 + order : ℕ) : ℝ) ^ order * ((q + 1 + 1 : ℕ) : ℝ) ^ (grade + 1)
              ≤ (((order + 2 : ℕ) : ℝ) * ((q + 1 : ℕ) : ℝ)) ^ order *
                  (((order + 2 : ℕ) : ℝ) * ((q + 1 : ℕ) : ℝ)) ^ (grade + 1) := by
                apply mul_le_mul
                · exact pow_le_pow_left₀ (Nat.cast_nonneg _) first_le order
                · exact pow_le_pow_left₀ (Nat.cast_nonneg _) second_le (grade + 1)
                · exact pow_nonneg (Nat.cast_nonneg _) _
                · exact pow_nonneg (by positivity) _
            _ = (((order + 2 : ℕ) : ℝ)) ^ (order + grade + 1) *
                  ((q + 1 : ℕ) : ℝ) ^ (order + grade + 1) := by
                have exponent_assoc : order + (grade + 1) = order + grade + 1 := by omega
                rw [← pow_add, mul_pow, exponent_assoc]
        have geometric_split : rootCollapseRatio x ^ (q + 1) =
            rootCollapseRatio x * rootCollapseRatio x ^ q := by
          rw [pow_succ]
          ring
        have square_nonneg : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
        have scale_nonneg : (0 : ℝ) ≤ ((rootCurveRadius x u w)⁻¹) ^ 2 *
            (6 * 4 ^ grade * rootEnvelopeScale x u w grade *
              rootEnvelopeScale x u w 0 ^ 2) := by
          have := rootEnvelopeScale_nonneg x u w grade
          have := rootEnvelopeScale_nonneg x u w 0
          positivity
        have ratio_pow_nonneg : (0 : ℝ) ≤ rootCollapseRatio x ^ q :=
          pow_nonneg ratio_pos.le q
        calc ((q + 1 + order : ℕ) : ℝ) ^ order *
              ((((rootCurveRadius x u w)⁻¹) ^ 2 * (6 * 4 ^ grade *
                rootEnvelopeScale x u w grade * rootEnvelopeScale x u w 0 ^ 2)) *
                (((q + 1 + 1 : ℕ) : ℝ) ^ (grade + 1) *
                  (t ^ 2 * rootCollapseRatio x ^ (q + 1))))
            = (((rootCurveRadius x u w)⁻¹) ^ 2 * (6 * 4 ^ grade *
                rootEnvelopeScale x u w grade * rootEnvelopeScale x u w 0 ^ 2)) *
                (t ^ 2 * rootCollapseRatio x) *
                ((((q + 1 + order : ℕ) : ℝ)) ^ order *
                  (((q + 1 + 1 : ℕ) : ℝ)) ^ (grade + 1) * rootCollapseRatio x ^ q) := by
              rw [geometric_split]
              ring
          _ ≤ (((rootCurveRadius x u w)⁻¹) ^ 2 * (6 * 4 ^ grade *
                rootEnvelopeScale x u w grade * rootEnvelopeScale x u w 0 ^ 2)) *
                (t ^ 2 * rootCollapseRatio x) *
                ((((order + 2 : ℕ) : ℝ)) ^ (order + grade + 1) *
                  (((q + 1 : ℕ) : ℝ)) ^ (order + grade + 1) * rootCollapseRatio x ^ q) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_right cast_le_one ratio_pow_nonneg
          _ = _ := by ring
    apply Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) comparison
    · have scale_nonneg := rootQuadScale_nonneg small u w grade (q + 1)
      have := sq_nonneg t
      have := pow_nonneg ratio_pos.le (q + 1)
      positivity
    · have coefficient_le := abs_rootDerivativeCoefficient_le order (q + 1)
      have payload_nonneg : (0 : ℝ) ≤
          t ^ 2 * (rootQuadScale x u w grade (q + 1) * rootCollapseRatio x ^ (q + 1)) := by
        have := rootQuadScale_nonneg small u w grade (q + 1)
        have := pow_nonneg ratio_pos.le (q + 1)
        have := sq_nonneg t
        positivity
      calc |rootDerivativeCoefficient order (q + 1)| *
            (t ^ 2 * (rootQuadScale x u w grade (q + 1) * rootCollapseRatio x ^ (q + 1)))
          ≤ ((q + 1 + order : ℕ) : ℝ) ^ order *
              (t ^ 2 * (rootQuadScale x u w grade (q + 1) *
                rootCollapseRatio x ^ (q + 1))) :=
            mul_le_mul_of_nonneg_right coefficient_le payload_nonneg
        _ = _ := by
            rw [scale_shape q]
            ring

/-- The exact quadratic bound of the shifted-series difference. -/
theorem rootShifted_difference_le (order : ℕ) {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (u w : TameCoefficient parameters)
    {t : ℝ} (inside : |t| ≤ rootCurveRadius x u w) (grade : ℕ) :
    coefficientEnvelope grade
      (tameRootShifted order (rootCurvePoint x u w t) - tameRootShifted order x -
        (t : ℂ) • (tameRootShifted (order + 1) x * u)) ≤
      t ^ 2 * ∑' q, |rootDerivativeCoefficient order (q + 1)| *
        (rootQuadScale x u w grade (q + 1) * rootCollapseRatio x ^ (q + 1)) := by
  have point_small := rootCurvePoint_lt_one small u w inside
  -- Rewrite the three total series as literal series.
  rw [tameRootShifted_of_small order point_small, tameRootShifted_of_small order small,
    tameRootShifted_of_small (order + 1) small]
  -- The difference of the first two series.
  rw [rootShiftedSeries, rootShiftedSeries,
    tameSeries_sub _ _ (rootSeriesMajorant_is_majorant order point_small)
      (rootSeriesMajorant_is_majorant order small)]
  -- The multiplied and scaled third series.
  rw [rootShiftedSeries, tameSeries_mul_fixed _ (rootSeriesMajorant_is_majorant
    (order + 1) small) u, tameSeries_const_smul]
  -- Drop the vanishing zeroth difference term.
  have zeroth_zero : (fun p => ((rootDerivativeCoefficient order p : ℝ) : ℂ) •
      (rootCurvePoint x u w t) ^ p - ((rootDerivativeCoefficient order p : ℝ) : ℂ) • x ^ p) 0 =
      0 := by
    show ((rootDerivativeCoefficient order 0 : ℝ) : ℂ) • (rootCurvePoint x u w t) ^ 0 -
      ((rootDerivativeCoefficient order 0 : ℝ) : ℂ) • x ^ 0 = 0
    rw [pow_zero, pow_zero, sub_self]
  rw [tameSeries_shift_of_zeroth_zero _ zeroth_zero]
  -- Combine into the remainder series.
  rw [tameSeries_sub _ _ ((rootSeriesMajorant_is_majorant order point_small).sub
      (rootSeriesMajorant_is_majorant order small)).shift
      ((rootSeriesMajorant_is_majorant (order + 1) small).mul_fixed u |>.const_smul (t : ℂ))]
  apply le_trans (le_of_eq (congrArg (coefficientEnvelope grade)
    (tameSeries_congr_terms _ (rootRemainder_series_majorant order small u w inside)
      (fun q => rootShifted_difference_terms order q u w t))))
  -- Envelope bound through the quadratic majorant.
  apply (tameSeries_envelope_le _ _ grade).trans
  rw [← tsum_mul_left]
  apply le_of_eq
  apply tsum_congr
  intro q
  ring

/-- The genuine envelope derivative of the shifted root series along the
quadratic curve: `G_{k+1}(x) · u`. -/
theorem hasEnvDerivAt_tameRootShifted (order : ℕ) {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (u w : TameCoefficient parameters) :
    HasEnvDerivAt (fun t => tameRootShifted order (rootCurvePoint x u w t))
      (tameRootShifted (order + 1) x * u) := by
  intro grade
  have radius_pos := rootCurveRadius_pos small u w
  set bound := ∑' q, |rootDerivativeCoefficient order (q + 1)| *
    (rootQuadScale x u w grade (q + 1) * rootCollapseRatio x ^ (q + 1)) with bound_def
  have near : ∀ᶠ (t : ℝ) in 𝓝[≠] (0 : ℝ), |t| ≤ rootCurveRadius x u w := by
    apply eventually_nhdsWithin_of_eventually_nhds
    have ball_mem := Metric.ball_mem_nhds (0 : ℝ) radius_pos
    apply Filter.eventually_of_mem ball_mem
    intro t membership
    have := Metric.mem_ball.mp membership
    rw [Real.dist_eq, sub_zero] at this
    exact this.le
  apply squeeze_zero' (Eventually.of_forall (fun _ => coefficientEnvelope_nonneg _ _))
    (g := fun t : ℝ => |t| * bound) ?_ ?_
  · apply near.mp
    apply eventually_nhdsWithin_of_forall
    intro t membership inside
    have nonzero : (t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by simpa using membership)
    have curve_zero : tameRootShifted order (rootCurvePoint x u w 0) =
        tameRootShifted order x := by rw [rootCurvePoint_zero]
    have algebra : ∀ (first second third : TameCoefficient parameters),
        (((t : ℂ))⁻¹ • (first - second)) - third =
          ((t : ℂ))⁻¹ • (first - second - (t : ℂ) • third) := by
      intro first second third
      rw [smul_sub (((t : ℂ))⁻¹) (first - second) ((t : ℂ) • third), smul_smul,
        inv_mul_cancel₀ nonzero, one_smul]
    have quotient_form : (((t : ℂ))⁻¹ •
        (tameRootShifted order (rootCurvePoint x u w t) -
          tameRootShifted order (rootCurvePoint x u w 0))) -
        tameRootShifted (order + 1) x * u =
        ((t : ℂ))⁻¹ • (tameRootShifted order (rootCurvePoint x u w t) -
          tameRootShifted order x -
          (t : ℂ) • (tameRootShifted (order + 1) x * u)) := by
      rw [curve_zero]
      exact algebra _ _ _
    rw [quotient_form, coefficientEnvelope_smul]
    have difference_le := rootShifted_difference_le order small u w inside grade
    rw [← bound_def] at difference_le
    calc ‖((t : ℂ))⁻¹‖ * coefficientEnvelope grade
          (tameRootShifted order (rootCurvePoint x u w t) - tameRootShifted order x -
            (t : ℂ) • (tameRootShifted (order + 1) x * u))
        ≤ ‖((t : ℂ))⁻¹‖ * (t ^ 2 * bound) :=
          mul_le_mul_of_nonneg_left difference_le (norm_nonneg _)
      _ = |t| * bound := by
          rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
          have abs_pos : (0 : ℝ) < |t| := abs_pos.mpr (by simpa using membership)
          rw [← sq_abs]
          field_simp
  · have limit : Tendsto (fun t : ℝ => |t| * bound) (𝓝 (0 : ℝ)) (𝓝 0) := by
      have shape : Tendsto (fun t : ℝ => |t| * bound) (𝓝 (0 : ℝ))
          (𝓝 (|(0 : ℝ)| * bound)) := (continuous_abs.mul continuous_const).tendsto 0
      simpa using shape
    exact limit.mono_left nhdsWithin_le_nhds

end Grad.NonlinearQuotientBounds
