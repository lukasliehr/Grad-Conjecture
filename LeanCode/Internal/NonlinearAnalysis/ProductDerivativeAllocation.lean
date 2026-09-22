import ProductClosedJet
import Mathlib.Analysis.Calculus.ContDiff.Bounds

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.NonlinearProduct

/-- Recursive finite Leibniz allocation. Each branch uses exactly the stated
total derivative order; no input is charged the total order independently. -/
def derivativeAllocation (arity : ℕ) : (Fin arity → ℕ → ℝ) → ℕ → ℝ :=
  Nat.rec (motive := fun count => (Fin count → ℕ → ℝ) → ℕ → ℝ)
    (fun _ order => if order = 0 then 1 else 0)
    (fun count previous sizes order =>
      ∑ split ∈ Finset.range (order + 1),
        (order.choose split : ℝ) *
          previous (fun index => sizes index.castSucc) split *
          sizes (Fin.last count) (order - split)) arity

theorem derivativeAllocation_zero (sizes : Fin 0 → ℕ → ℝ) (order : ℕ) :
    derivativeAllocation 0 sizes order = if order = 0 then 1 else 0 := rfl

theorem derivativeAllocation_succ (arity : ℕ) (sizes : Fin (arity + 1) → ℕ → ℝ) (order : ℕ) :
    derivativeAllocation (arity + 1) sizes order =
      ∑ split ∈ Finset.range (order + 1), (order.choose split : ℝ) *
        derivativeAllocation arity (fun index => sizes index.castSucc) split *
          sizes (Fin.last arity) (order - split) := rfl

theorem derivativeAllocation_nonnegative {arity : ℕ}
    (sizes : Fin arity → ℕ → ℝ) (nonnegative : ∀ index order, 0 ≤ sizes index order)
    (order : ℕ) : 0 ≤ derivativeAllocation arity sizes order := by
  induction arity generalizing order with
  | zero => rw [derivativeAllocation_zero]; split <;> norm_num
  | succ arity inductionHypothesis =>
    rw [derivativeAllocation_succ]
    exact Finset.sum_nonneg (fun split _ => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (inductionHypothesis _
        (fun index rank => nonnegative index.castSucc rank) split)) (nonnegative _ _))

def allocationMultiplicity (arity order : ℕ) : ℝ :=
  derivativeAllocation arity (fun _ _ => 1) order

theorem allocationMultiplicity_nonnegative (arity order : ℕ) :
    0 ≤ allocationMultiplicity arity order :=
  derivativeAllocation_nonnegative _ (fun _ _ => zero_le_one) _

/-- A uniform bound for each genuine total-order allocation bounds the full
Leibniz sum. The extra multiplier avoids divisions and includes zero factors. -/
theorem derivativeAllocation_le_of_allocation_bound {arity : ℕ}
    (sizes : Fin arity → ℕ → ℝ) (nonnegative : ∀ index rank, 0 ≤ sizes index rank)
    (order : ℕ) (multiplier bound : ℝ) (multiplierNonnegative : 0 ≤ multiplier)
    (allocatedBound : ∀ orders : Fin arity → ℕ, (∑ index, orders index) = order →
      multiplier * ∏ index, sizes index (orders index) ≤ bound) :
    multiplier * derivativeAllocation arity sizes order ≤ allocationMultiplicity arity order * bound := by
  induction arity generalizing order multiplier with
  | zero =>
    by_cases zeroOrder : order = 0
    · subst order
      simpa [derivativeAllocation_zero, allocationMultiplicity] using
        allocatedBound (fun index => Fin.elim0 index) (by simp)
    · simp [derivativeAllocation_zero, allocationMultiplicity, zeroOrder]
  | succ arity inductionHypothesis =>
    simp only [allocationMultiplicity, derivativeAllocation_succ, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro split splitMembership
    have splitBound : split ≤ order := Nat.le_of_lt_succ (Finset.mem_range.mp splitMembership)
    have smaller : (multiplier * sizes (Fin.last arity) (order - split)) *
        derivativeAllocation arity (fun index => sizes index.castSucc) split ≤
        allocationMultiplicity arity split * bound := by
      apply inductionHypothesis _ (fun index rank => nonnegative index.castSucc rank)
        split _ (mul_nonneg multiplierNonnegative (nonnegative _ _))
      intro orders ordersTotal
      have fullTotal : (∑ index, Fin.snoc orders (order - split) index) = order := by
        rw [Fin.sum_univ_castSucc]
        simpa only [Fin.snoc_castSucc, Fin.snoc_last, ordersTotal] using Nat.add_sub_of_le splitBound
      have fullBound := allocatedBound (Fin.snoc orders (order - split)) fullTotal
      rw [Fin.prod_univ_castSucc] at fullBound
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at fullBound
      nlinarith only [fullBound]
    calc
      _ = (order.choose split : ℝ) *
          ((multiplier * sizes (Fin.last arity) (order - split)) *
            derivativeAllocation arity (fun index => sizes index.castSucc) split) := by ring
      _ ≤ (order.choose split : ℝ) * (allocationMultiplicity arity split * bound) :=
        mul_le_mul_of_nonneg_left smaller (Nat.cast_nonneg _)
      _ = _ := by simp only [allocationMultiplicity]; ring

theorem multilinear_iterated_derivative_allocation
    {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℝ Source]
    (arity : ℕ) {Spaces : Fin arity → Type}
    [∀ index, NormedAddCommGroup (Spaces index)] [∀ index, NormedSpace ℝ (Spaces index)]
    {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (multiplication : ContinuousMultilinearMap ℝ Spaces Value)
    (fields : (index : Fin arity) → Source → Spaces index)
    (smooth : ∀ index, ContDiff ℝ ∞ (fields index)) (order : ℕ) (point : Source) :
    ‖iteratedFDeriv ℝ order (fun source => multiplication (fun index => fields index source)) point‖ ≤
      ‖multiplication‖ * derivativeAllocation arity
        (fun index rank => ‖iteratedFDeriv ℝ rank (fields index) point‖) order := by
  induction arity generalizing Value order with
  | zero =>
    have constant : (fun source => multiplication (fun index => fields index source)) =
        fun _ : Source => multiplication (fun index => Fin.elim0 index) := by
      funext source
      congr 1
      exact Subsingleton.elim _ _
    rw [constant]
    by_cases zeroOrder : order = 0
    · subst order
      rw [norm_iteratedFDeriv_zero]
      simpa [derivativeAllocation_zero] using multiplication.le_opNorm (fun index => Fin.elim0 index)
    · simp only [iteratedFDeriv_const_of_ne zeroOrder, Pi.zero_apply, norm_zero,
        derivativeAllocation_zero, if_neg zeroOrder, mul_zero, le_refl]
  | succ arity inductionHypothesis =>
    have curriedSmooth : ContDiff ℝ ∞
        (fun source => multiplication.curryRight (fun index => fields index.castSucc source)) :=
      multiplication.curryRight.contDiff.comp (contDiff_pi.mpr (fun index => smooth index.castSucc))
    have exactCurry : (fun source => multiplication (fun index => fields index source)) =
        fun source => multiplication.curryRight
          (fun index => fields index.castSucc source) (fields (Fin.last arity) source) := by
      funext source
      rw [ContinuousMultilinearMap.curryRight_apply]
      congr 1
      exact (Fin.snoc_init_self _).symm
    rw [exactCurry]
    apply (norm_iteratedFDeriv_clm_apply curriedSmooth (smooth (Fin.last arity)) point
      (by exact_mod_cast le_top)).trans
    calc
      _ ≤ ∑ split ∈ Finset.range (order + 1),
          (order.choose split : ℝ) *
            (‖multiplication‖ * derivativeAllocation arity
              (fun index rank => ‖iteratedFDeriv ℝ rank (fields index.castSucc) point‖) split) *
            ‖iteratedFDeriv ℝ (order - split) (fields (Fin.last arity)) point‖ := by
        apply Finset.sum_le_sum
        intro split _
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        simpa only [ContinuousMultilinearMap.curryRight_norm] using
          inductionHypothesis multiplication.curryRight
            (fun index => fields index.castSucc) (fun index => smooth index.castSucc) split
      _ = _ := by
        rw [derivativeAllocation_succ, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro split _
        ring

end Grad.NonlinearProduct
