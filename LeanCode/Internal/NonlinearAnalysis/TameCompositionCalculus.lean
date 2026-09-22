import TameCompositionState

noncomputable section

set_option maxHeartbeats 1600000

open Filter
open scoped BigOperators Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.Constraints

/-! # Calculus of the bounded multilinear parts

Joint continuity of a multilinear map with a one-high bound, in the state
grade norms, and the product rule along genuinely differentiable curves: the
ordinary Leibniz rule for the five homogeneous parts of the literal quotient
polynomial, in the difference-quotient sense of the accepted derivative
families. -/

variable {parameters : PhaseParameters}

/-! ### Mixed tuples and telescoping -/

/-- The mixed tuple: the upper values on the first `count` slots, the lower
values elsewhere. -/
def mixedTuple {slots : ℕ} (upper lower : Fin slots → QuotientState parameters)
    (count : ℕ) : Fin slots → QuotientState parameters :=
  fun slot => if (slot : ℕ) < count then upper slot else lower slot

theorem mixedTuple_zero {slots : ℕ} (upper lower : Fin slots → QuotientState parameters) :
    mixedTuple upper lower 0 = lower :=
  funext fun _ => if_neg (Nat.not_lt_zero _)

theorem mixedTuple_top {slots : ℕ} (upper lower : Fin slots → QuotientState parameters)
    {count : ℕ} (enough : slots ≤ count) : mixedTuple upper lower count = upper :=
  funext fun slot => if_pos (lt_of_lt_of_le slot.isLt enough)

theorem mixedTuple_apply_self {slots : ℕ} (upper lower : Fin slots → QuotientState parameters)
    (slot : Fin slots) : mixedTuple upper lower (slot : ℕ) slot = lower slot :=
  if_neg (lt_irrefl _)

theorem mixedTuple_succ {slots : ℕ} (upper lower : Fin slots → QuotientState parameters)
    (slot : Fin slots) :
    mixedTuple upper lower ((slot : ℕ) + 1) =
      Function.update (mixedTuple upper lower (slot : ℕ)) slot (upper slot) := by
  funext other
  unfold mixedTuple
  by_cases equal : other = slot
  · subst equal
    rw [Function.update_self, if_pos (Nat.lt_succ_self _)]
  · rw [Function.update_of_ne equal]
    have ne_val : (other : ℕ) ≠ slot := fun h => equal (Fin.ext h)
    by_cases below : (other : ℕ) < slot
    · rw [if_pos (Nat.lt_succ_of_lt below), if_pos below]
    · rw [if_neg below, if_neg (by omega)]

/-- One telescoping step of a multilinear map along the mixed tuples. -/
theorem multilinear_mixed_step {slots : ℕ}
    (P : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters) (QuotientRows parameters))
    (upper lower : Fin slots → QuotientState parameters) (slot : Fin slots) :
    P (mixedTuple upper lower ((slot : ℕ) + 1)) - P (mixedTuple upper lower (slot : ℕ)) =
      P (Function.update (mixedTuple upper lower (slot : ℕ)) slot (upper slot - lower slot)) := by
  have self : Function.update (mixedTuple upper lower (slot : ℕ)) slot (lower slot) =
      mixedTuple upper lower (slot : ℕ) := by
    rw [← mixedTuple_apply_self upper lower slot, Function.update_eq_self]
  calc P (mixedTuple upper lower ((slot : ℕ) + 1)) - P (mixedTuple upper lower (slot : ℕ))
      = P (Function.update (mixedTuple upper lower (slot : ℕ)) slot (upper slot)) -
          P (Function.update (mixedTuple upper lower (slot : ℕ)) slot (lower slot)) := by
        rw [mixedTuple_succ, self]
    _ = P (Function.update (mixedTuple upper lower (slot : ℕ)) slot (upper slot - lower slot)) :=
        (MultilinearMap.map_update_sub P _ slot _ _).symm

/-- The exact telescoping of a multilinear difference into single-slot
differences, indexed by the slots. -/
theorem multilinear_sub_eq_sum {slots : ℕ}
    (P : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters) (QuotientRows parameters))
    (upper lower : Fin slots → QuotientState parameters) :
    P upper - P lower = ∑ slot : Fin slots,
      P (Function.update (mixedTuple upper lower (slot : ℕ)) slot (upper slot - lower slot)) := by
  have telescope := Finset.sum_range_sub (fun count => P (mixedTuple upper lower count)) slots
  rw [mixedTuple_top upper lower le_rfl, mixedTuple_zero] at telescope
  rw [← telescope, ← Fin.sum_univ_eq_sum_range
    (fun count => P (mixedTuple upper lower (count + 1)) - P (mixedTuple upper lower count)) slots]
  exact Finset.sum_congr rfl fun slot _ => multilinear_mixed_step P upper lower slot

/-! ### Convergence in the state norms -/

/-- Convergence of the state norm under convergence of the difference. -/
theorem stateNorm_tendsto_of_sub {ι : Type*} {filter : Filter ι} (grade : ℕ)
    (curve : ι → QuotientState parameters) (limit : QuotientState parameters)
    (converges : Tendsto (fun index => stateNorm grade (curve index - limit)) filter (𝓝 0)) :
    Tendsto (fun index => stateNorm grade (curve index)) filter (𝓝 (stateNorm grade limit)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun index => ?_) converges
  rw [Real.norm_eq_abs]
  exact abs_stateNorm_sub_le grade _ _

/-- The one-high argument sum vanishes when one slot is zero. -/
theorem oneHighArgumentSum_update_zero (grade : ℕ) {slots : ℕ}
    (arguments : Fin slots → QuotientState parameters) (slot : Fin slots) :
    oneHighArgumentSum grade (Function.update arguments slot 0) = 0 := by
  unfold oneHighArgumentSum
  apply Finset.sum_eq_zero
  intro other _
  by_cases equal : other = slot
  · subst equal
    rw [Function.update_self, stateNorm_zero, zero_mul]
  · apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm equal, Finset.mem_univ slot⟩)
    rw [Function.update_self, stateNorm_zero]

/-- The one-high bound of a part on every single-slot update; vacuous for a
part without slots (the constant part). -/
def OneHighBounded {slots : ℕ}
    (P : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters) (QuotientRows parameters)) :
    Prop :=
  ∀ grade : ℕ, ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (arguments : Fin slots → QuotientState parameters) (slot : Fin slots)
      (value : QuotientState parameters),
      rowsGradeNorm grade (P (Function.update arguments slot value)) ≤
        constant * oneHighArgumentSum grade (Function.update arguments slot value)

/-- A part bounded on all argument tuples is one-high bounded. -/
theorem oneHighBounded_of_bound {slots : ℕ}
    (P : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters) (QuotientRows parameters))
    (bounded : ∀ grade : ℕ, ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ arguments, rowsGradeNorm grade (P arguments) ≤ constant * oneHighArgumentSum grade arguments) :
    OneHighBounded P := by
  intro grade
  obtain ⟨constant, nonneg, bound⟩ := bounded grade
  exact ⟨constant, nonneg, fun arguments slot value => bound _⟩

/-- A part without slots is one-high bounded vacuously. -/
theorem oneHighBounded_zero
    (P : MultilinearMap ℂ (fun _ : Fin 0 => QuotientState parameters) (QuotientRows parameters)) :
    OneHighBounded P :=
  fun _ => ⟨0, le_rfl, fun _ slot _ => slot.elim0⟩

/-- Slotwise convergence of tuples: every slot converges in every grade. -/
def TuplesTendsto {ι : Type*} {slots : ℕ} (tuples : ι → Fin slots → QuotientState parameters)
    (limit : Fin slots → QuotientState parameters) (filter : Filter ι) : Prop :=
  ∀ (slot : Fin slots) (grade : ℕ),
    Tendsto (fun index => stateNorm grade (tuples index slot - limit slot)) filter (𝓝 0)

/-- Joint continuity of a one-high bounded multilinear map: slotwise
convergence in every grade gives convergence of the values in every grade. -/
theorem multilinear_tendsto_of_tuples {ι : Type*} {filter : Filter ι} {slots : ℕ}
    (P : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters) (QuotientRows parameters))
    (bounded : OneHighBounded P)
    (tuples : ι → Fin slots → QuotientState parameters)
    (limit : Fin slots → QuotientState parameters)
    (converges : TuplesTendsto tuples limit filter) (grade : ℕ) :
    Tendsto (fun index => rowsGradeNorm grade (P (tuples index) - P limit)) filter (𝓝 0) := by
  obtain ⟨constant, constant_nonneg, bound⟩ := bounded grade
  have factorTendsto : ∀ (slot other : Fin slots) (r : ℕ),
      Tendsto (fun index => stateNorm r (Function.update (mixedTuple (tuples index) limit
        (slot : ℕ)) slot (tuples index slot - limit slot) other)) filter
        (𝓝 (stateNorm r (Function.update limit slot 0 other))) := by
    intro slot other r
    by_cases equal : other = slot
    · subst equal
      simp only [Function.update_self, stateNorm_zero]
      exact converges other r
    · simp only [Function.update_of_ne equal]
      apply stateNorm_tendsto_of_sub
      by_cases below : (other : ℕ) < slot
      · have form : ∀ index, mixedTuple (tuples index) limit (slot : ℕ) other = tuples index other :=
          fun index => if_pos below
        simp only [form]
        exact converges other r
      · have form : ∀ index, mixedTuple (tuples index) limit (slot : ℕ) other = limit other :=
          fun index => if_neg below
        simp only [form, sub_self, stateNorm_zero]
        exact tendsto_const_nhds
  have sumBound : ∀ index, rowsGradeNorm grade (P (tuples index) - P limit) ≤
      ∑ slot : Fin slots, constant * oneHighArgumentSum grade
        (Function.update (mixedTuple (tuples index) limit (slot : ℕ)) slot
          (tuples index slot - limit slot)) := by
    intro index
    rw [multilinear_sub_eq_sum]
    exact (rowsGradeNorm_sum_le grade _ _).trans (Finset.sum_le_sum fun slot _ => bound _ _ _)
  have majorant : Tendsto (fun index => ∑ slot : Fin slots, constant * oneHighArgumentSum grade
      (Function.update (mixedTuple (tuples index) limit (slot : ℕ)) slot
        (tuples index slot - limit slot))) filter
      (𝓝 (∑ slot : Fin slots, constant * oneHighArgumentSum grade (Function.update limit slot 0))) := by
    apply tendsto_finsetSum
    intro slot _
    apply Tendsto.const_mul
    unfold oneHighArgumentSum
    apply tendsto_finsetSum
    intro other _
    exact (factorTendsto slot other (grade + 6)).mul
      (tendsto_finsetProd _ fun third _ => factorTendsto slot third 4)
  have zero : (∑ slot : Fin slots, constant * oneHighArgumentSum grade
      (Function.update limit slot 0)) = 0 := by
    simp only [oneHighArgumentSum_update_zero, mul_zero, Finset.sum_const_zero]
  rw [zero] at majorant
  exact squeeze_zero (fun _ => rowsGradeNorm_nonneg _ _) sumBound majorant

/-- A genuinely differentiable curve converges to its base value. -/
theorem curve_sub_tendsto (curve : ℝ → QuotientState parameters)
    (value derivative : QuotientState parameters) (grade : ℕ)
    (differentiable : Tendsto (fun t : ℝ => stateNorm grade
      ((((t : ℂ))⁻¹ • (curve t - value)) - derivative)) (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun t : ℝ => stateNorm grade (curve t - value)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have identity : ∀ t : ℝ, t ≠ 0 → curve t - value =
      (t : ℂ) • (((((t : ℂ))⁻¹ • (curve t - value)) - derivative) + derivative) := by
    intro t nonzero
    have tC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
    rw [sub_add_cancel, smul_smul, mul_inv_cancel₀ tC, one_smul]
  have absTendsto : Tendsto (fun t : ℝ => |t|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have := (continuous_abs.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    rwa [abs_zero] at this
  have majorant : Tendsto (fun t : ℝ => |t| * (stateNorm grade
      ((((t : ℂ))⁻¹ • (curve t - value)) - derivative) + stateNorm grade derivative))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have := absTendsto.mul (differentiable.add (tendsto_const_nhds (x := stateNorm grade derivative)))
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun _ => stateNorm_nonneg _ _) ?_ majorant
  filter_upwards [self_mem_nhdsWithin] with t nonzero
  calc stateNorm grade (curve t - value)
      = stateNorm grade ((t : ℂ) • (((((t : ℂ))⁻¹ • (curve t - value)) - derivative) + derivative)) :=
        congrArg (stateNorm grade) (identity t nonzero)
    _ = |t| * stateNorm grade (((((t : ℂ))⁻¹ • (curve t - value)) - derivative) + derivative) := by
        rw [stateNorm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |t| * (stateNorm grade ((((t : ℂ))⁻¹ • (curve t - value)) - derivative) +
          stateNorm grade derivative) :=
        mul_le_mul_of_nonneg_left (stateNorm_add_le grade _ _) (abs_nonneg t)

/-- The product rule: a one-high bounded multilinear map along genuinely
differentiable curves has the Leibniz sum of single-slot derivatives as
genuine derivative, in every grade. -/
theorem multilinear_product_rule {slots : ℕ}
    (P : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters) (QuotientRows parameters))
    (bounded : OneHighBounded P)
    (curves : Fin slots → ℝ → QuotientState parameters)
    (values derivatives : Fin slots → QuotientState parameters)
    (differentiable : ∀ (slot : Fin slots) (grade : ℕ), Tendsto (fun t : ℝ => stateNorm grade
      ((((t : ℂ))⁻¹ • (curves slot t - values slot)) - derivatives slot)) (𝓝[≠] (0 : ℝ)) (𝓝 0))
    (grade : ℕ) :
    Tendsto (fun t : ℝ => rowsGradeNorm grade
      ((((t : ℂ))⁻¹ • (P (fun slot => curves slot t) - P values)) -
        ∑ slot, P (Function.update values slot (derivatives slot)))) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  set quotientTuple : ℝ → Fin slots → Fin slots → QuotientState parameters := fun t slot =>
    Function.update (mixedTuple (fun other => curves other t) values (slot : ℕ)) slot
      (((t : ℂ))⁻¹ • (curves slot t - values slot)) with quotientTuple_def
  have expression : ∀ t : ℝ,
      (((t : ℂ))⁻¹ • (P (fun slot => curves slot t) - P values)) -
        ∑ slot, P (Function.update values slot (derivatives slot)) =
      ∑ slot, (P (quotientTuple t slot) - P (Function.update values slot (derivatives slot))) := by
    intro t
    rw [multilinear_sub_eq_sum, Finset.smul_sum, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro slot _
    simp only [quotientTuple_def]
    exact (MultilinearMap.map_update_smul P _ slot _ _).symm
  have eachTendsto : ∀ slot : Fin slots, Tendsto (fun t : ℝ => rowsGradeNorm grade
      (P (quotientTuple t slot) - P (Function.update values slot (derivatives slot))))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    intro slot
    apply multilinear_tendsto_of_tuples P bounded (fun t => quotientTuple t slot)
      (Function.update values slot (derivatives slot))
    intro other r
    by_cases equal : other = slot
    · subst equal
      simp only [quotientTuple_def, Function.update_self]
      exact differentiable other r
    · simp only [quotientTuple_def, Function.update_of_ne equal]
      by_cases below : (other : ℕ) < slot
      · have form : ∀ t : ℝ,
            mixedTuple (fun third => curves third t) values (slot : ℕ) other = curves other t :=
          fun t => if_pos below
        simp only [form]
        exact curve_sub_tendsto (curves other) (values other) (derivatives other) r
          (differentiable other r)
      · have form : ∀ t : ℝ,
            mixedTuple (fun third => curves third t) values (slot : ℕ) other = values other :=
          fun t => if_neg below
        simp only [form, sub_self, stateNorm_zero]
        exact tendsto_const_nhds
  have sumTendsto : Tendsto (fun t : ℝ => ∑ slot, rowsGradeNorm grade
      (P (quotientTuple t slot) - P (Function.update values slot (derivatives slot))))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have := tendsto_finsetSum Finset.univ (fun slot _ => eachTendsto slot)
    simpa using this
  refine squeeze_zero (fun _ => rowsGradeNorm_nonneg _ _) (fun t => ?_) sumTendsto
  rw [expression t]
  exact rowsGradeNorm_sum_le grade _ _

end Grad.NonlinearQuotientBounds
