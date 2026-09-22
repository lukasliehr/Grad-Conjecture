import MajorantInterface

/-!
# NG_F06: the N3 placement estimate for the exponential derivative terms

The accepted composition bound `‖A ∘ B‖ ≤ K ‖A‖ ‖B‖` (`coefficientComposition_norm_le`,
`K = gradeProductConstant grade`) gives, for every ordered composition word
of `p` factors applied to the graded identity `I`,
`‖f_0 ∘ ⋯ ∘ f_{p-1} (I)‖ ≤ ‖I‖ K^p ∏_k ‖f_k‖`. For a placement of the `j`
directions among the `p` slots the factor product is `‖A‖^{p-j} ∏_i ‖h_i‖`,
and there are exactly `p^{\underline j}` placements (`Fintype.card_embedding_eq`),
so the derivative term `(p!)⁻¹ Σ_placements word` has norm at most
`‖I‖ (p^{\underline j} / p!) K^p R^{p-j} ∏_i ‖h_i‖` on the ball `‖A‖ ≤ R`.
The order-zero terms are the accepted `seedExponentialTerm A p = (p!)⁻¹ • A^p`.
-/

noncomputable section

open scoped BigOperators

namespace Grad.CoefficientMajorants

open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.Frame
open Grad.Constraints.Seed

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}

local instance coefficientComplexSpace :
    NormedSpace ℂ (Coefficient L sigma gamma ell grade dimension dimension) := inferInstance

/-- The composition word of constant factors is the accepted graded power. -/
theorem compositionWord_const (base : Coefficient L sigma gamma ell grade dimension dimension)
    (p : ℕ) :
    compositionWord admissible p (fun _ => base) =
      gradedCoefficientPower admissible base p := by
  induction p with
  | zero => rfl
  | succ p inductionHypothesis =>
    rw [compositionWord, gradedCoefficientPower_succ]
    exact congrArg (coefficientComposition admissible grade base) inductionHypothesis

/-- The ordered composition word bound `‖I‖ K^p ∏_k ‖f_k‖`. -/
theorem compositionWord_norm_le (p : ℕ)
    (factors : Fin p → Coefficient L sigma gamma ell grade dimension dimension) :
    ‖compositionWord admissible p factors‖ ≤
      ‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖ *
        gradeProductConstant grade ^ p * ∏ index, ‖factors index‖ := by
  induction p with
  | zero =>
    rw [compositionWord, Fin.prod_univ_zero, pow_zero, mul_one, mul_one]
  | succ p inductionHypothesis =>
    rw [compositionWord]
    have constantNonneg := seedProductConstant_nonnegative grade
    calc ‖coefficientComposition admissible grade (factors 0)
          (compositionWord admissible p (Fin.tail factors))‖
        ≤ gradeProductConstant grade * ‖factors 0‖ *
            ‖compositionWord admissible p (Fin.tail factors)‖ :=
          coefficientComposition_norm_le admissible grade _ _
      _ ≤ gradeProductConstant grade * ‖factors 0‖ *
            (‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖ *
              gradeProductConstant grade ^ p * ∏ index, ‖Fin.tail factors index‖) :=
          mul_le_mul_of_nonneg_left (inductionHypothesis (Fin.tail factors))
            (mul_nonneg constantNonneg (norm_nonneg _))
      _ = ‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖ *
            gradeProductConstant grade ^ (p + 1) * ∏ index, ‖factors index‖ := by
          rw [Fin.prod_univ_succ, pow_succ]
          simp only [Fin.tail]
          ring

/-- A placed slot carries its direction. -/
theorem placedFactor_placement {order p : ℕ} (placement : Fin order ↪ Fin p)
    (base : Coefficient L sigma gamma ell grade dimension dimension)
    (directions : Fin order → Coefficient L sigma gamma ell grade dimension dimension)
    (index : Fin order) :
    placedFactor placement base directions (placement index) = directions index := by
  unfold placedFactor
  have hit : ∃ other, placement other = placement index := ⟨index, rfl⟩
  rw [dif_pos hit]
  exact congrArg directions (placement.injective (Classical.choose_spec hit))

/-- An unplaced slot carries the base element. -/
theorem placedFactor_of_not_mem {order p : ℕ} (placement : Fin order ↪ Fin p)
    (base : Coefficient L sigma gamma ell grade dimension dimension)
    (directions : Fin order → Coefficient L sigma gamma ell grade dimension dimension)
    (slot : Fin p) (miss : slot ∉ Finset.univ.map placement) :
    placedFactor placement base directions slot = base := by
  unfold placedFactor
  rw [dif_neg]
  rintro ⟨index, hit⟩
  exact miss (Finset.mem_map.mpr ⟨index, Finset.mem_univ _, hit⟩)

/-- The factor product of a placement on the ball: `R^{p-j} ∏_i ‖h_i‖`. -/
theorem prod_norm_placedFactor_le {order p : ℕ} (placement : Fin order ↪ Fin p)
    {radius : ℝ} {base : Coefficient L sigma gamma ell grade dimension dimension}
    (baseLe : ‖base‖ ≤ radius)
    (directions : Fin order → Coefficient L sigma gamma ell grade dimension dimension) :
    ∏ slot, ‖placedFactor placement base directions slot‖ ≤
      radius ^ (p - order) * ∏ index, ‖directions index‖ := by
  rw [← Finset.prod_mul_prod_compl (Finset.univ.map placement)]
  have first : ∏ slot ∈ Finset.univ.map placement,
      ‖placedFactor placement base directions slot‖ = ∏ index, ‖directions index‖ := by
    rw [Finset.prod_map]
    apply Finset.prod_congr rfl
    intro index _
    rw [placedFactor_placement]
  have second : ∏ slot ∈ (Finset.univ.map placement)ᶜ,
      ‖placedFactor placement base directions slot‖ = ‖base‖ ^ (p - order) := by
    rw [Finset.prod_congr rfl (fun slot membership => by
      rw [placedFactor_of_not_mem placement base directions slot (Finset.mem_compl.mp membership)])]
    rw [Finset.prod_const, Finset.card_compl, Finset.card_map,
      Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  rw [first, second, mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) baseLe _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)

/-- The order-zero derivative terms are the accepted exponential summands. -/
theorem exponentialDerivativeTerm_zero
    (base : Coefficient L sigma gamma ell grade dimension dimension) (p : ℕ) :
    exponentialDerivativeTerm admissible 0 p base (fun index => index.elim0) =
      seedExponentialTerm admissible base p := by
  unfold exponentialDerivativeTerm seedExponentialTerm
  congr 1
  have each : ∀ placement : Fin 0 ↪ Fin p,
      compositionWord admissible p
        (placedFactor placement base (fun index => index.elim0)) =
      gradedCoefficientPower admissible base p := by
    intro placement
    rw [← compositionWord_const admissible base p]
    congr 1
  rw [Finset.sum_congr rfl (fun placement _ => each placement), Finset.sum_const,
    Finset.card_univ, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin,
    Nat.descFactorial_zero, one_nsmul]

set_option maxHeartbeats 800000 in
/-- The N3 placement estimate: the norm of the derivative term is dominated by
the explicit factorial-denominator majorant times `∏_i ‖h_i‖`, uniformly on
the ball `‖A‖ ≤ R`. -/
theorem exponentialDerivativeTerm_norm_le (order p : ℕ) {radius : ℝ}
    (radiusNonneg : 0 ≤ radius) {base : Coefficient L sigma gamma ell grade dimension dimension}
    (baseLe : ‖base‖ ≤ radius)
    (directions : Fin order → Coefficient L sigma gamma ell grade dimension dimension) :
    ‖exponentialDerivativeTerm admissible order p base directions‖ ≤
      expOperatorMajorant grade ‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖
          radius order p *
        ∏ index, ‖directions index‖ := by
  unfold exponentialDerivativeTerm expOperatorMajorant
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  have constantNonneg := seedProductConstant_nonnegative grade
  have termNonneg : 0 ≤ ‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖ *
      gradeProductConstant grade ^ p * (radius ^ (p - order) * ∏ index, ‖directions index‖) := by
    apply mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg constantNonneg _))
    exact mul_nonneg (pow_nonneg radiusNonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have factorialNonneg : 0 ≤ ((p.factorial : ℕ) : ℝ)⁻¹ := by positivity
  calc ((p.factorial : ℕ) : ℝ)⁻¹ *
        ‖∑ placement : Fin order ↪ Fin p,
          compositionWord admissible p (placedFactor placement base directions)‖
      ≤ ((p.factorial : ℕ) : ℝ)⁻¹ * ∑ placement : Fin order ↪ Fin p,
          ‖compositionWord admissible p (placedFactor placement base directions)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) factorialNonneg
    _ ≤ ((p.factorial : ℕ) : ℝ)⁻¹ * ∑ _placement : Fin order ↪ Fin p,
          ‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖ *
            gradeProductConstant grade ^ p *
              (radius ^ (p - order) * ∏ index, ‖directions index‖) := by
        apply mul_le_mul_of_nonneg_left _ factorialNonneg
        apply Finset.sum_le_sum
        intro placement _
        exact (compositionWord_norm_le admissible p _).trans
          (mul_le_mul_of_nonneg_left (prod_norm_placedFactor_le placement baseLe directions)
            (mul_nonneg (norm_nonneg _) (pow_nonneg constantNonneg _)))
    _ = ((p.factorial : ℕ) : ℝ)⁻¹ * ((p.descFactorial order : ℕ) : ℝ) *
          (‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖ *
            gradeProductConstant grade ^ p *
              (radius ^ (p - order) * ∏ index, ‖directions index‖)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        ring
    _ = _ := by
        rw [div_eq_mul_inv]
        ring

end Grad.CoefficientMajorants
