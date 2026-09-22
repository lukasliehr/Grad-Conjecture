import TameRootQuadratic

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The double binomial collapse of the decorated monomial grid and the
final quadratic-in-`t` bound of the root curve remainder. -/

variable {parameters : PhaseParameters}

theorem coefficientEnvelope_sum_le {Index : Type} (grade : ℕ) (indices : Finset Index)
    (values : Index → TameCoefficient parameters) :
    coefficientEnvelope grade (∑ index ∈ indices, values index) ≤
      ∑ index ∈ indices, coefficientEnvelope grade (values index) := by
  induction indices using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, coefficientEnvelope_zero]
  | cons head tail absent inductive_step =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact (coefficientEnvelope_add_le grade _ _).trans
      (add_le_add le_rfl inductive_step)

/-- One decorated grid payload with the radius powers built in. -/
def rootGridPayload (x u w : TameCoefficient parameters) (p d l : ℕ) : ℝ :=
  (p.choose d : ℝ) * rootSmallRadius x ^ (p - d) *
    ((d.choose l : ℝ) * (rootCurveRadius x u w * rootDirectionSize u) ^ l *
      ((rootCurveRadius x u w) ^ 2 * rootDirectionSize w) ^ (d - l))

theorem rootGridPayload_nonneg {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (u w : TameCoefficient parameters) (p d l : ℕ) :
    0 ≤ rootGridPayload x u w p d l := by
  have radius_nonneg := rootCurveRadius_nonneg small u w
  have base_nonneg := (rootSmallRadius_pos x).le
  have sizeU_nonneg := (rootDirectionSize_pos u).le
  have sizeW_nonneg := (rootDirectionSize_pos w).le
  rw [rootGridPayload]
  positivity

/-- The scale of the quadratic remainder bound. -/
def rootQuadScale (x u w : TameCoefficient parameters) (grade p : ℕ) : ℝ :=
  ((rootCurveRadius x u w)⁻¹) ^ 2 *
    (6 * 4 ^ grade * ((p + 1 : ℕ) : ℝ) ^ (grade + 1) *
      rootEnvelopeScale x u w grade * rootEnvelopeScale x u w 0 ^ 2)

theorem rootQuadScale_nonneg {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (u w : TameCoefficient parameters)
    (grade p : ℕ) : 0 ≤ rootQuadScale x u w grade p := by
  have radius_pos := rootCurveRadius_pos small u w
  have scaleG := rootEnvelopeScale_nonneg x u w grade
  have scaleZ := rootEnvelopeScale_nonneg x u w 0
  rw [rootQuadScale]
  positivity

/-- The decorated monomial estimate: quadratic in the parameter, with the
grid payload separated. -/
theorem rootCurveMonomial_envelope_le {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (u w : TameCoefficient parameters)
    (grade p d l : ℕ) (low_le : l ≤ d) (drop_le : d ≤ p)
    (quadratic : 2 ≤ l + 2 * (d - l)) {t : ℝ}
    (inside : |t| ≤ rootCurveRadius x u w) :
    coefficientEnvelope grade (rootCurveMonomial x u w t p d l) ≤
      t ^ 2 * (rootQuadScale x u w grade p * rootGridPayload x u w p d l) := by
  set radius := rootCurveRadius x u w with radius_def
  have radius_pos : 0 < radius := rootCurveRadius_pos small u w
  set exponent := l + 2 * (d - l) with exponent_def
  have norm_scalar : ‖((((p.choose d) * (d.choose l) : ℕ) : ℂ) *
      ((t : ℂ)) ^ exponent)‖ = ((p.choose d : ℝ) * (d.choose l : ℝ)) * |t| ^ exponent := by
    rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      Nat.cast_mul]
  have envelope_eq : coefficientEnvelope grade (rootCurveMonomial x u w t p d l) =
      (((p.choose d : ℝ) * (d.choose l : ℝ)) * |t| ^ exponent) *
        coefficientEnvelope grade (x ^ (p - d) * (u ^ l * w ^ (d - l))) := by
    rw [rootCurveMonomial, coefficientEnvelope_smul, norm_scalar]
  have index_eq : (p - d) + l + (d - l) + 1 = p + 1 := by omega
  have triple_le := rootTriple_envelope_le small u w grade (p - d) l (d - l)
  rw [index_eq] at triple_le
  have abs_power_le : |t| ^ exponent ≤ t ^ 2 * radius ^ (exponent - 2) := by
    have split : |t| ^ exponent = |t| ^ 2 * |t| ^ (exponent - 2) := by
      rw [← pow_add]
      congr 1
      omega
    have tail_le : |t| ^ (exponent - 2) ≤ radius ^ (exponent - 2) :=
      pow_le_pow_left₀ (abs_nonneg t) inside _
    calc |t| ^ exponent = |t| ^ 2 * |t| ^ (exponent - 2) := split
      _ ≤ |t| ^ 2 * radius ^ (exponent - 2) :=
          mul_le_mul_of_nonneg_left tail_le (pow_nonneg (abs_nonneg t) 2)
      _ = t ^ 2 * radius ^ (exponent - 2) := by rw [sq_abs]
  have radius_power_eq : radius ^ (exponent - 2) =
      (radius⁻¹) ^ 2 * (radius ^ l * (radius ^ 2) ^ (d - l)) := by
    have combine : radius ^ l * (radius ^ 2) ^ (d - l) = radius ^ exponent := by
      rw [← pow_mul, ← pow_add]
    rw [combine]
    have expand : radius ^ exponent = radius ^ 2 * radius ^ (exponent - 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [expand]
    field_simp
  set scaleBlock := 6 * (4 : ℝ) ^ grade * ((p + 1 : ℕ) : ℝ) ^ (grade + 1) *
    rootEnvelopeScale x u w grade * rootEnvelopeScale x u w 0 ^ 2 with scaleBlock_def
  have scaleBlock_nonneg : 0 ≤ scaleBlock := by
    have := rootEnvelopeScale_nonneg x u w grade
    have := rootEnvelopeScale_nonneg x u w 0
    rw [scaleBlock_def]
    positivity
  have payload_nonneg : (0 : ℝ) ≤ rootSmallRadius x ^ (p - d) *
      rootDirectionSize u ^ l * rootDirectionSize w ^ (d - l) := by
    have := (rootSmallRadius_pos x).le
    have := (rootDirectionSize_pos u).le
    have := (rootDirectionSize_pos w).le
    positivity
  have choose_nonneg : (0 : ℝ) ≤ (p.choose d : ℝ) * (d.choose l : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc coefficientEnvelope grade (rootCurveMonomial x u w t p d l)
      = (((p.choose d : ℝ) * (d.choose l : ℝ)) * |t| ^ exponent) *
        coefficientEnvelope grade (x ^ (p - d) * (u ^ l * w ^ (d - l))) := envelope_eq
    _ ≤ (((p.choose d : ℝ) * (d.choose l : ℝ)) * |t| ^ exponent) *
        (scaleBlock * (rootSmallRadius x ^ (p - d) * rootDirectionSize u ^ l *
          rootDirectionSize w ^ (d - l))) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg choose_nonneg
          (pow_nonneg (abs_nonneg t) exponent))
        calc coefficientEnvelope grade (x ^ (p - d) * (u ^ l * w ^ (d - l)))
            ≤ 6 * 4 ^ grade * ((p + 1 : ℕ) : ℝ) ^ (grade + 1) *
                rootEnvelopeScale x u w grade * rootEnvelopeScale x u w 0 ^ 2 *
                (rootSmallRadius x ^ (p - d) * rootDirectionSize u ^ l *
                  rootDirectionSize w ^ (d - l)) := triple_le
          _ = _ := by rw [scaleBlock_def]
    _ ≤ (((p.choose d : ℝ) * (d.choose l : ℝ)) * (t ^ 2 * radius ^ (exponent - 2))) *
        (scaleBlock * (rootSmallRadius x ^ (p - d) * rootDirectionSize u ^ l *
          rootDirectionSize w ^ (d - l))) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg scaleBlock_nonneg payload_nonneg)
        exact mul_le_mul_of_nonneg_left abs_power_le choose_nonneg
    _ = t ^ 2 * ((radius⁻¹ ^ 2 * scaleBlock) *
        ((p.choose d : ℝ) * rootSmallRadius x ^ (p - d) *
          ((d.choose l : ℝ) * (radius ^ l * rootDirectionSize u ^ l) *
            ((radius ^ 2) ^ (d - l) * rootDirectionSize w ^ (d - l))))) := by
        rw [radius_power_eq]
        ring
    _ = _ := by
        rw [rootQuadScale, rootGridPayload, ← radius_def, mul_pow, mul_pow]

/-- The double binomial collapse of the payload grid. -/
theorem rootGridPayload_collapse (x u w : TameCoefficient parameters) (p : ℕ) :
    (∑ d ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (d + 1),
      rootGridPayload x u w p d l) =
      (rootCurveRadius x u w * rootDirectionSize u +
        (rootCurveRadius x u w) ^ 2 * rootDirectionSize w + rootSmallRadius x) ^ p := by
  rw [add_pow]
  have reindex : ∀ d ∈ Finset.range (p + 1),
      (∑ l ∈ Finset.range (d + 1), rootGridPayload x u w p d l) =
      (rootCurveRadius x u w * rootDirectionSize u +
        (rootCurveRadius x u w) ^ 2 * rootDirectionSize w) ^ d *
        rootSmallRadius x ^ (p - d) * (p.choose d : ℝ) := by
    intro d _
    rw [add_pow, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    rw [rootGridPayload]
    ring
  rw [Finset.sum_congr rfl reindex]

/-- The collapsed base stays below the strict ratio inside the radius. -/
theorem rootGrid_base_le {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (u w : TameCoefficient parameters) :
    rootCurveRadius x u w * rootDirectionSize u +
        (rootCurveRadius x u w) ^ 2 * rootDirectionSize w + rootSmallRadius x ≤
      rootCollapseRatio x := by
  have radius_nonneg := rootCurveRadius_nonneg small u w
  have radius_le_one := rootCurveRadius_le_one x u w
  have square_le : (rootCurveRadius x u w) ^ 2 ≤ rootCurveRadius x u w := by
    calc (rootCurveRadius x u w) ^ 2 = rootCurveRadius x u w * rootCurveRadius x u w := by
          ring
      _ ≤ 1 * rootCurveRadius x u w :=
          mul_le_mul_of_nonneg_right radius_le_one radius_nonneg
      _ = _ := one_mul _
  have w_term_le : (rootCurveRadius x u w) ^ 2 * rootDirectionSize w ≤
      rootCurveRadius x u w * rootDirectionSize w :=
    mul_le_mul_of_nonneg_right square_le (rootDirectionSize_pos w).le
  have budget := rootCurveRadius_directions_le small u w
  have expand : rootCurveRadius x u w * rootDirectionSize u +
      rootCurveRadius x u w * rootDirectionSize w =
      rootCurveRadius x u w * (rootDirectionSize u + rootDirectionSize w) := by ring
  rw [rootCollapseRatio]
  linarith [budget, w_term_le, expand]

theorem rootGrid_base_nonneg {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (u w : TameCoefficient parameters) :
    0 ≤ rootCurveRadius x u w * rootDirectionSize u +
        (rootCurveRadius x u w) ^ 2 * rootDirectionSize w + rootSmallRadius x := by
  have radius_nonneg := rootCurveRadius_nonneg small u w
  have := (rootDirectionSize_pos u).le
  have := (rootDirectionSize_pos w).le
  have := (rootSmallRadius_pos x).le
  positivity

/-- The final quadratic remainder estimate in every graded envelope. -/
theorem rootCurveRemainder_envelope_le {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (u w : TameCoefficient parameters)
    (grade q : ℕ) {t : ℝ} (inside : |t| ≤ rootCurveRadius x u w) :
    coefficientEnvelope grade (rootCurveRemainder x u w t q) ≤
      t ^ 2 * (rootQuadScale x u w grade (q + 1) *
        rootCollapseRatio x ^ (q + 1)) := by
  have payload_nonneg := rootGridPayload_nonneg small u w
  have scale_nonneg := rootQuadScale_nonneg small u w grade (q + 1)
  have square_nonneg : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  -- Per-term bounds over the remainder index set.
  have inner_bound : ∀ inner ∈ Finset.range q, ∀ low ∈ Finset.range (inner + 3),
      coefficientEnvelope grade (rootCurveMonomial x u w t (q + 1) (inner + 2) low) ≤
      t ^ 2 * (rootQuadScale x u w grade (q + 1) *
        rootGridPayload x u w (q + 1) (inner + 2) low) := by
    intro inner inner_mem low low_mem
    have inner_lt := Finset.mem_range.mp inner_mem
    have low_lt := Finset.mem_range.mp low_mem
    exact rootCurveMonomial_envelope_le small u w grade (q + 1) (inner + 2) low
      (by omega) (by omega) (by omega) inside
  have linear_bound : coefficientEnvelope grade
      (rootCurveMonomial x u w t (q + 1) 1 0) ≤
      t ^ 2 * (rootQuadScale x u w grade (q + 1) * rootGridPayload x u w (q + 1) 1 0) :=
    rootCurveMonomial_envelope_le small u w grade (q + 1) 1 0
      (by omega) (by omega) (by omega) inside
  -- The remainder-set payload total is dominated by the full grid.
  have full_peel₁ := Finset.sum_range_succ' (fun d => ∑ l ∈ Finset.range (d + 1),
    rootGridPayload x u w (q + 1) d l) (q + 1)
  have full_peel₂ := Finset.sum_range_succ' (fun d => ∑ l ∈ Finset.range (d + 2),
    rootGridPayload x u w (q + 1) (d + 1) l) q
  have one_split : (∑ l ∈ Finset.range 2, rootGridPayload x u w (q + 1) 1 l) =
      rootGridPayload x u w (q + 1) 1 0 + rootGridPayload x u w (q + 1) 1 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
  have payload_total_le :
      (∑ inner ∈ Finset.range q, ∑ low ∈ Finset.range (inner + 3),
        rootGridPayload x u w (q + 1) (inner + 2) low) +
        rootGridPayload x u w (q + 1) 1 0 ≤
      ∑ d ∈ Finset.range (q + 2), ∑ l ∈ Finset.range (d + 1),
        rootGridPayload x u w (q + 1) d l := by
    rw [full_peel₁, full_peel₂, one_split]
    have zero_nonneg : 0 ≤ ∑ l ∈ Finset.range 1, rootGridPayload x u w (q + 1) 0 l :=
      Finset.sum_nonneg (fun l _ => payload_nonneg (q + 1) 0 l)
    have one_one_nonneg : 0 ≤ rootGridPayload x u w (q + 1) 1 1 :=
      payload_nonneg (q + 1) 1 1
    linarith
  have collapse := rootGridPayload_collapse x u w (q + 1)
  have base_pow_le : (rootCurveRadius x u w * rootDirectionSize u +
      (rootCurveRadius x u w) ^ 2 * rootDirectionSize w + rootSmallRadius x) ^ (q + 1) ≤
      rootCollapseRatio x ^ (q + 1) :=
    pow_le_pow_left₀ (rootGrid_base_nonneg small u w) (rootGrid_base_le small u w) _
  calc coefficientEnvelope grade (rootCurveRemainder x u w t q)
      ≤ coefficientEnvelope grade
          (∑ inner ∈ Finset.range q, ∑ low ∈ Finset.range (inner + 3),
            rootCurveMonomial x u w t (q + 1) (inner + 2) low) +
        coefficientEnvelope grade (rootCurveMonomial x u w t (q + 1) 1 0) := by
        rw [rootCurveRemainder_eq]
        exact coefficientEnvelope_add_le grade _ _
    _ ≤ (∑ inner ∈ Finset.range q, ∑ low ∈ Finset.range (inner + 3),
          t ^ 2 * (rootQuadScale x u w grade (q + 1) *
            rootGridPayload x u w (q + 1) (inner + 2) low)) +
        t ^ 2 * (rootQuadScale x u w grade (q + 1) *
          rootGridPayload x u w (q + 1) 1 0) := by
        apply add_le_add _ linear_bound
        apply le_trans (coefficientEnvelope_sum_le grade _ _)
        apply Finset.sum_le_sum
        intro inner inner_mem
        apply le_trans (coefficientEnvelope_sum_le grade _ _)
        exact Finset.sum_le_sum (fun low low_mem => inner_bound inner inner_mem low low_mem)
    _ = t ^ 2 * (rootQuadScale x u w grade (q + 1) *
        ((∑ inner ∈ Finset.range q, ∑ low ∈ Finset.range (inner + 3),
          rootGridPayload x u w (q + 1) (inner + 2) low) +
          rootGridPayload x u w (q + 1) 1 0)) := by
        rw [mul_add, mul_add]
        congr 1
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro inner _
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ t ^ 2 * (rootQuadScale x u w grade (q + 1) *
        ((rootCurveRadius x u w * rootDirectionSize u +
          (rootCurveRadius x u w) ^ 2 * rootDirectionSize w +
            rootSmallRadius x) ^ (q + 1))) := by
        apply mul_le_mul_of_nonneg_left _ square_nonneg
        apply mul_le_mul_of_nonneg_left _ scale_nonneg
        rw [← collapse]
        exact payload_total_le
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ square_nonneg
        exact mul_le_mul_of_nonneg_left base_pow_le scale_nonneg

end Grad.NonlinearQuotientBounds
