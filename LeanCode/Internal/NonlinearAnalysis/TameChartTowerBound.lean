import TameChartPerm

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The one-high envelope bound of the chart tower: the shifted-root slope
bound uniform over the base ball, per-factor bounds, the generalized head
product induction, and the master per-term estimate in the term's own
index list. -/

variable {parameters : PhaseParameters}

/-- The graded envelope of the quadratic. -/
theorem tangentQuadratic_envelope_le (grade : ℕ) (base : TangentCoefficient parameters) :
    coefficientEnvelope grade (tangentQuadratic base) ≤
      (2 : ℝ) ^ (grade + 1) *
        (tangentPlanarEnvelope grade base * tangentPlanarEnvelope 0 base) := by
  calc coefficientEnvelope grade (tangentQuadratic base)
      = ‖((2 : ℂ))⁻¹‖ * coefficientEnvelope grade (tangentDot base base) := by
        rw [tangentQuadratic, coefficientEnvelope_smul]
    _ ≤ ‖((2 : ℂ))⁻¹‖ * ((2 : ℝ) ^ (grade + 1) *
        (tangentPlanarEnvelope grade base * tangentPlanarEnvelope 0 base +
          tangentPlanarEnvelope 0 base * tangentPlanarEnvelope grade base)) :=
        mul_le_mul_of_nonneg_left (tangentDot_envelope_le grade base base) (norm_nonneg _)
    _ = _ := by
        rw [norm_inv, Complex.norm_ofNat]
        ring

theorem tangentQuadratic_envelope_zero_le (base : TangentCoefficient parameters) :
    coefficientEnvelope 0 (tangentQuadratic base) ≤
      tangentPlanarEnvelope 0 base * tangentPlanarEnvelope 0 base := by
  calc coefficientEnvelope 0 (tangentQuadratic base)
      = ‖((2 : ℂ))⁻¹‖ * coefficientEnvelope 0 (tangentDot base base) := by
        rw [tangentQuadratic, coefficientEnvelope_smul]
    _ ≤ ‖((2 : ℂ))⁻¹‖ *
        (2 * (tangentPlanarEnvelope 0 base * tangentPlanarEnvelope 0 base)) :=
        mul_le_mul_of_nonneg_left (tangentDot_envelope_zero_le base base) (norm_nonneg _)
    _ = _ := by
        rw [norm_inv, Complex.norm_ofNat]
        ring

/-- The uniform slope bound of the shifted root series. -/
def rootSlopeBound (order grade : ℕ) (ratio : ℝ) : ℝ :=
  ∑' p, |rootDerivativeCoefficient order (p + 1)| *
    ((p + 1 : ℕ) : ℝ) ^ (grade + 1) * ratio ^ p

theorem rootSlope_summable (order grade : ℕ) {ratio : ℝ}
    (ratioPos : 0 < ratio) (ratioLt : ratio < 1) :
    Summable (fun p : ℕ => |rootDerivativeCoefficient order (p + 1)| *
      ((p + 1 : ℕ) : ℝ) ^ (grade + 1) * ratio ^ p) := by
  have comparison : Summable (fun p : ℕ =>
      (((order + 2 : ℕ) : ℝ)) ^ (order + grade + 1) *
        (((p + 1 : ℕ) : ℝ) ^ (order + grade + 1) * ratio ^ p)) :=
    Summable.mul_left _ (summable_succ_pow_mul_geometric (order + grade + 1) ratioPos ratioLt)
  apply Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) comparison
  · have := abs_nonneg (rootDerivativeCoefficient order (p + 1))
    have := pow_nonneg ratioPos.le p
    positivity
  · have coefficient_le := abs_rootDerivativeCoefficient_le order (p + 1)
    have first_le : ((p + 1 + order : ℕ) : ℝ) ≤
        ((order + 2 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) p, Nat.cast_nonneg (α := ℝ) order]
    have second_le : ((p + 1 : ℕ) : ℝ) ≤ ((order + 2 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ) := by
      have one_le : (1 : ℝ) ≤ ((order + 2 : ℕ) : ℝ) := by
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) order]
      nlinarith [Nat.cast_nonneg (α := ℝ) p]
    have ratio_pow_nonneg : (0 : ℝ) ≤ ratio ^ p := pow_nonneg ratioPos.le p
    calc |rootDerivativeCoefficient order (p + 1)| *
          ((p + 1 : ℕ) : ℝ) ^ (grade + 1) * ratio ^ p
        ≤ ((p + 1 + order : ℕ) : ℝ) ^ order *
            ((p + 1 : ℕ) : ℝ) ^ (grade + 1) * ratio ^ p := by
          apply mul_le_mul_of_nonneg_right _ ratio_pow_nonneg
          exact mul_le_mul_of_nonneg_right coefficient_le
            (pow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ ((((order + 2 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) ^ order *
            (((order + 2 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) ^ (grade + 1)) * ratio ^ p := by
          apply mul_le_mul_of_nonneg_right _ ratio_pow_nonneg
          exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) first_le order)
            (pow_le_pow_left₀ (Nat.cast_nonneg _) second_le (grade + 1))
            (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (by positivity) _)
      _ = _ := by
          have exponent_assoc : order + (grade + 1) = order + grade + 1 := by omega
          rw [← pow_add, mul_pow, exponent_assoc]
          ring

theorem rootSlopeBound_nonneg (order grade : ℕ) {ratio : ℝ}
    (ratioPos : 0 < ratio) : 0 ≤ rootSlopeBound order grade ratio := by
  apply tsum_nonneg
  intro p
  have := abs_nonneg (rootDerivativeCoefficient order (p + 1))
  have := pow_nonneg ratioPos.le p
  positivity

/-- The shifted root series against the uniform slope. -/
theorem tameRootShifted_envelope_le_slope (order grade : ℕ)
    {x : TameCoefficient parameters} (small : coefficientEnvelope 0 x < 1)
    {ratio : ℝ} (ratioLt : ratio < 1) (radius_le : rootSmallRadius x ≤ ratio) :
    coefficientEnvelope grade (tameRootShifted order x) ≤
      |rootDerivativeCoefficient order 0| * Real.exp parameters.sigma0 +
        rootSlopeBound order grade ratio * coefficientEnvelope grade x := by
  have ratioPos : 0 < ratio := lt_of_lt_of_le (rootSmallRadius_pos x) radius_le
  have majorant_summable := rootSeriesMajorant_summable order small grade
  rw [tameRootShifted_of_small order small]
  apply (rootShiftedSeries_envelope_le order x small grade).trans
  rw [majorant_summable.tsum_eq_zero_add]
  apply add_le_add
  · rw [rootSeriesMajorant]
  · have pointwise (p : ℕ) : rootSeriesMajorant order x grade (p + 1) ≤
        |rootDerivativeCoefficient order (p + 1)| *
          ((p + 1 : ℕ) : ℝ) ^ (grade + 1) * ratio ^ p * coefficientEnvelope grade x := by
      rw [rootSeriesMajorant]
      have radius_pow_le : rootSmallRadius x ^ p ≤ ratio ^ p :=
        pow_le_pow_left₀ (rootSmallRadius_pos x).le radius_le p
      have envelope_nonneg := coefficientEnvelope_nonneg grade x
      calc |rootDerivativeCoefficient order (p + 1)| *
            (((p + 1 : ℕ) : ℝ) ^ (grade + 1) * rootSmallRadius x ^ p *
              coefficientEnvelope grade x)
          ≤ |rootDerivativeCoefficient order (p + 1)| *
              (((p + 1 : ℕ) : ℝ) ^ (grade + 1) * ratio ^ p *
                coefficientEnvelope grade x) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            apply mul_le_mul_of_nonneg_right _ envelope_nonneg
            exact mul_le_mul_of_nonneg_left radius_pow_le
              (pow_nonneg (Nat.cast_nonneg _) _)
        _ = _ := by ring
    calc (∑' p, rootSeriesMajorant order x grade (p + 1))
        ≤ ∑' p, |rootDerivativeCoefficient order (p + 1)| *
            ((p + 1 : ℕ) : ℝ) ^ (grade + 1) * ratio ^ p * coefficientEnvelope grade x := by
          apply Summable.tsum_le_tsum pointwise
            ((summable_nat_add_iff 1).mpr majorant_summable)
            ((rootSlope_summable order grade ratioPos ratioLt).mul_right _)
      _ = _ := by
          rw [rootSlopeBound, ← tsum_mul_right]

/-! ### The generalized head product bound -/

/-- The recursive one-high value of a high/low bound list. -/
noncomputable def oneHighValue : List (ℝ × ℝ) → ℝ
  | [] => 0
  | (high, low) :: rest => high * (rest.map Prod.snd).prod + low * oneHighValue rest

theorem oneHighValue_nonneg : ∀ bounds : List (ℝ × ℝ),
    (∀ pair ∈ bounds, 0 ≤ pair.1 ∧ 0 ≤ pair.2) → 0 ≤ oneHighValue bounds := by
  intro bounds
  induction bounds with
  | nil =>
    intro _
    rw [oneHighValue]
  | cons head tail inductive_step =>
    intro nonneg
    obtain ⟨left, right⟩ := nonneg head List.mem_cons_self
    have tail_nonneg := inductive_step
      (fun pair membership => nonneg pair (List.mem_cons_of_mem head membership))
    have prod_nonneg : 0 ≤ (tail.map Prod.snd).prod := by
      apply List.prod_nonneg
      intro value membership
      obtain ⟨pair, pair_mem, pair_eq⟩ := List.mem_map.mp membership
      exact pair_eq ▸ (nonneg pair (List.mem_cons_of_mem head pair_mem)).2
    match head with
    | (high, low) =>
      rw [oneHighValue]
      exact add_nonneg (mul_nonneg left prod_nonneg) (mul_nonneg right tail_nonneg)

/-- The generalized head-times-list product bound: the head carries its own
high/low data and the constant grows by one binary split per factor. -/
theorem head_list_prod_envelope_le (grade : ℕ) :
    ∀ (factors : List (TameCoefficient parameters × ℝ × ℝ))
      (head : TameCoefficient parameters) (headHigh headLow : ℝ),
    coefficientEnvelope grade head ≤ headHigh →
    coefficientEnvelope 0 head ≤ headLow →
    (∀ triple ∈ factors, coefficientEnvelope grade triple.1 ≤ triple.2.1 ∧
      coefficientEnvelope 0 triple.1 ≤ triple.2.2) →
    (∀ triple ∈ factors, 0 ≤ triple.2.1 ∧ 0 ≤ triple.2.2) →
    0 ≤ headHigh → 0 ≤ headLow →
    coefficientEnvelope grade (head * (factors.map (fun triple => triple.1)).prod) ≤
      ((2 : ℝ) ^ grade) ^ factors.length *
        (headHigh * (factors.map (fun triple => triple.2.2)).prod +
          headLow * oneHighValue (factors.map (fun triple => triple.2))) := by
  intro factors
  induction factors with
  | nil =>
    intro head headHigh headLow head_high_le _ _ _ _ headLow_nonneg
    rw [List.map_nil, List.prod_nil, mul_one, List.map_nil, List.prod_nil, List.map_nil]
    rw [oneHighValue, List.length_nil, pow_zero, one_mul, mul_one, mul_zero, add_zero]
    exact head_high_le
  | cons headFactor tail inductive_step =>
    intro head headHigh headLow head_high_le head_low_le factor_bounds factor_nonneg
      headHigh_nonneg headLow_nonneg
    obtain ⟨factor_high_le, factor_low_le⟩ := factor_bounds headFactor List.mem_cons_self
    obtain ⟨factorHigh_nonneg, factorLow_nonneg⟩ := factor_nonneg headFactor List.mem_cons_self
    have combined_high : coefficientEnvelope grade (head * headFactor.1) ≤
        (2 : ℝ) ^ grade * (headHigh * headFactor.2.2 + headLow * headFactor.2.1) := by
      apply (tameMul_envelope_le grade head headFactor.1).trans
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) grade)
      apply add_le_add
      · exact mul_le_mul head_high_le factor_low_le (coefficientEnvelope_nonneg 0 _)
          headHigh_nonneg
      · exact mul_le_mul head_low_le factor_high_le (coefficientEnvelope_nonneg grade _)
          headLow_nonneg
    have combined_low : coefficientEnvelope 0 (head * headFactor.1) ≤
        headLow * headFactor.2.2 :=
      (tameMul_envelope_zero_le head headFactor.1).trans
        (mul_le_mul head_low_le factor_low_le (coefficientEnvelope_nonneg 0 _) headLow_nonneg)
    have tail_step := inductive_step (head * headFactor.1)
      ((2 : ℝ) ^ grade * (headHigh * headFactor.2.2 + headLow * headFactor.2.1))
      (headLow * headFactor.2.2) combined_high combined_low
      (fun triple membership => factor_bounds triple (List.mem_cons_of_mem headFactor membership))
      (fun triple membership => factor_nonneg triple (List.mem_cons_of_mem headFactor membership))
      (by positivity) (mul_nonneg headLow_nonneg factorLow_nonneg)
    have regroup : head * ((headFactor :: tail).map (fun triple => triple.1)).prod =
        (head * headFactor.1) * (tail.map (fun triple => triple.1)).prod := by
      rw [List.map_cons, List.prod_cons]
      ring
    rw [regroup]
    apply tail_step.trans
    have lows_nonneg : 0 ≤ (tail.map (fun triple => triple.2.2)).prod := by
      apply List.prod_nonneg
      intro value membership
      obtain ⟨triple, triple_mem, triple_eq⟩ := List.mem_map.mp membership
      exact triple_eq ▸ (factor_nonneg triple (List.mem_cons_of_mem headFactor triple_mem)).2
    have oneHigh_nonneg : 0 ≤ oneHighValue (tail.map (fun triple => triple.2)) := by
      apply oneHighValue_nonneg
      intro pair membership
      obtain ⟨triple, triple_mem, triple_eq⟩ := List.mem_map.mp membership
      exact triple_eq ▸ factor_nonneg triple (List.mem_cons_of_mem headFactor triple_mem)
    calc ((2 : ℝ) ^ grade) ^ tail.length *
          (((2 : ℝ) ^ grade * (headHigh * headFactor.2.2 + headLow * headFactor.2.1)) *
            (tail.map (fun triple => triple.2.2)).prod +
            (headLow * headFactor.2.2) * oneHighValue (tail.map (fun triple => triple.2)))
        ≤ ((2 : ℝ) ^ grade) ^ tail.length * ((2 : ℝ) ^ grade *
            ((headHigh * headFactor.2.2 + headLow * headFactor.2.1) *
              (tail.map (fun triple => triple.2.2)).prod +
              (headLow * headFactor.2.2) *
                oneHighValue (tail.map (fun triple => triple.2)))) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (pow_nonneg (by norm_num) grade) _)
          have two_pow_one_le : (1 : ℝ) ≤ (2 : ℝ) ^ grade := one_le_pow₀ (by norm_num)
          nlinarith [mul_nonneg (mul_nonneg headLow_nonneg factorLow_nonneg) oneHigh_nonneg,
            mul_nonneg (add_nonneg (mul_nonneg headHigh_nonneg factorLow_nonneg)
              (mul_nonneg headLow_nonneg factorHigh_nonneg)) lows_nonneg]
      _ = _ := by
          rw [List.length_cons, pow_succ, List.map_cons, List.prod_cons, List.map_cons,
            oneHighValue]
          have snd_map : (tail.map (fun triple => triple.2)).map Prod.snd =
              tail.map (fun triple => triple.2.2) := by
            rw [List.map_map]
            rfl
          rw [snd_map]
          ring

end Grad.NonlinearQuotientBounds
