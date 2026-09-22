import BKB11TupleWeights

noncomputable section

open scoped BigOperators ENNReal

namespace Grad.BoundaryKernelAction

/-- Iterated scalar convolution on the genuine two-frequency displacement
group.  The word has `count + 1` factors, in written composition order. -/
def twoFrequencyScalarWord {count : ℕ} :
    (Fin (count + 1) → (ℤ × ℤ) → ℝ≥0∞) → (ℤ × ℤ) → ℝ≥0∞ :=
  Nat.rec
    (motive := fun total =>
      (Fin (total + 1) → (ℤ × ℤ) → ℝ≥0∞) → (ℤ × ℤ) → ℝ≥0∞)
    (fun factors shift => factors 0 shift)
    (fun _ recursed factors total => ∑' middle,
      factors 0 middle *
        recursed (fun index => factors index.succ) (total - middle))
    count

theorem twoFrequencyScalarWord_zero
    (factors : Fin 1 → (ℤ × ℤ) → ℝ≥0∞) (shift : ℤ × ℤ) :
    twoFrequencyScalarWord factors shift = factors 0 shift := rfl

theorem twoFrequencyScalarWord_succ {inner : ℕ}
    (factors : Fin (inner + 2) → (ℤ × ℤ) → ℝ≥0∞)
    (total : ℤ × ℤ) :
    twoFrequencyScalarWord factors total = ∑' middle,
      factors 0 middle *
        twoFrequencyScalarWord (fun index => factors index.succ) (total - middle) := rfl

/-- Weighted mass of a two-frequency scalar word as an unconditional tuple
sum.  Working in `ENNReal` avoids any circular summability premise. -/
theorem twoFrequencyScalarWord_weighted : ∀ {count : ℕ}
    (factors : Fin (count + 1) → (ℤ × ℤ) → ℝ≥0∞)
    (weight : (ℤ × ℤ) → ℝ≥0∞),
    (∑' total, weight total * twoFrequencyScalarWord factors total) =
      ∑' tuple : Fin (count + 1) → (ℤ × ℤ),
        weight (∑ index, tuple index) *
          ∏ index, factors index (tuple index) := by
  intro count
  induction count with
  | zero =>
      intro factors weight
      rw [← (Equiv.funUnique (Fin 1) (ℤ × ℤ)).symm.tsum_eq
        (f := fun tuple : Fin 1 → (ℤ × ℤ) =>
          weight (∑ index, tuple index) *
            ∏ index, factors index (tuple index))]
      apply tsum_congr
      intro shift
      show weight shift * factors 0 shift =
        weight (∑ _index : Fin 1, shift) *
          ∏ _index : Fin 1, factors _index shift
      rw [Fin.sum_univ_one, Fin.prod_univ_one]
  | succ inner innerHypothesis =>
      intro factors weight
      calc
        (∑' total, weight total * twoFrequencyScalarWord factors total) =
            ∑' total, ∑' middle,
              weight total * (factors 0 middle *
                twoFrequencyScalarWord (fun index => factors index.succ)
                  (total - middle)) := by
          apply tsum_congr
          intro total
          rw [twoFrequencyScalarWord_succ, ENNReal.tsum_mul_left]
        _ = ∑' middle, ∑' total,
              weight total * (factors 0 middle *
                twoFrequencyScalarWord (fun index => factors index.succ)
                  (total - middle)) := ENNReal.tsum_comm
        _ = ∑' middle, ∑' rest,
              weight (middle + rest) * (factors 0 middle *
                twoFrequencyScalarWord (fun index => factors index.succ) rest) := by
          apply tsum_congr
          intro middle
          rw [← (Equiv.addLeft middle).tsum_eq
            (f := fun total => weight total * (factors 0 middle *
              twoFrequencyScalarWord (fun index => factors index.succ)
                (total - middle)))]
          apply tsum_congr
          intro rest
          change weight (middle + rest) *
              (factors 0 middle *
                twoFrequencyScalarWord (fun index => factors index.succ)
                  (middle + rest - middle)) = _
          rw [add_sub_cancel_left]
        _ = ∑' middle, factors 0 middle * ∑' rest,
              (fun tail => weight (middle + tail)) rest *
                twoFrequencyScalarWord (fun index => factors index.succ) rest := by
          apply tsum_congr
          intro middle
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro rest
          ring
        _ = ∑' middle, factors 0 middle *
              ∑' tuple : Fin (inner + 1) → (ℤ × ℤ),
                weight (middle + ∑ index, tuple index) *
                  ∏ index, factors index.succ (tuple index) := by
          apply tsum_congr
          intro middle
          rw [innerHypothesis (fun index => factors index.succ)
            (fun rest => weight (middle + rest))]
        _ = ∑' pair : (ℤ × ℤ) ×
              (Fin (inner + 1) → (ℤ × ℤ)),
              weight (pair.1 + ∑ index, pair.2 index) *
                (factors 0 pair.1 *
                  ∏ index, factors index.succ (pair.2 index)) := by
          rw [ENNReal.tsum_prod
            (f := fun middle (tuple : Fin (inner + 1) → (ℤ × ℤ)) =>
              weight (middle + ∑ index, tuple index) *
                (factors 0 middle *
                  ∏ index, factors index.succ (tuple index)))]
          apply tsum_congr
          intro middle
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro tuple
          ring
        _ = ∑' tuple : Fin (inner + 2) → (ℤ × ℤ),
              weight (∑ index, tuple index) *
                ∏ index, factors index (tuple index) := by
          rw [← (Fin.consEquiv
            (fun _ : Fin (inner + 2) => (ℤ × ℤ))).tsum_eq
            (f := fun tuple : Fin (inner + 2) → (ℤ × ℤ) =>
              weight (∑ index, tuple index) *
                ∏ index, factors index (tuple index))]
          apply tsum_congr
          intro pair
          show weight (pair.1 + ∑ index, pair.2 index) *
                (factors 0 pair.1 *
                  ∏ index, factors index.succ (pair.2 index)) =
              weight (∑ index,
                (Fin.consEquiv
                  (fun _ : Fin (inner + 2) => (ℤ × ℤ))) pair index) *
                ∏ index, factors index
                  ((Fin.consEquiv
                    (fun _ : Fin (inner + 2) => (ℤ × ℤ))) pair index)
          conv_rhs => rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
          simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]

/-- Extended-real Fubini for finite tuples of two-frequency shifts. -/
theorem twoFrequencyTuple_tsum_prod {count : ℕ}
    (factors : Fin count → (ℤ × ℤ) → ℝ≥0∞) :
    (∑' tuple : Fin count → (ℤ × ℤ),
      ∏ index, factors index (tuple index)) =
      ∏ index, ∑' shift, factors index shift := by
  induction count with
  | zero =>
      have rhsOne : (∏ index : Fin 0, ∑' shift, factors index shift) = 1 := by
        rw [Finset.univ_eq_empty, Finset.prod_empty]
      have summandOne : ∀ tuple : Fin 0 → (ℤ × ℤ),
          (∏ index, factors index (tuple index)) = 1 := by
        intro tuple
        rw [Finset.univ_eq_empty, Finset.prod_empty]
      rw [rhsOne, tsum_congr summandOne,
        tsum_eq_single (fun index => index.elim0)
          (fun tuple different =>
            absurd (funext (fun index => index.elim0)) different)]
  | succ inner innerHypothesis =>
      calc
        (∑' tuple : Fin (inner + 1) → (ℤ × ℤ),
            ∏ index, factors index (tuple index)) =
            ∑' pair : (ℤ × ℤ) ×
                (Fin inner → (ℤ × ℤ)),
              factors 0 pair.1 *
                ∏ index : Fin inner, factors index.succ (pair.2 index) := by
          rw [← (Fin.consEquiv
            (fun _ : Fin (inner + 1) => (ℤ × ℤ))).tsum_eq
            (f := fun tuple : Fin (inner + 1) → (ℤ × ℤ) =>
              ∏ index, factors index (tuple index))]
          apply tsum_congr
          intro pair
          rw [Fin.prod_univ_succ]
          simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
        _ = ∑' shift, ∑' rest : Fin inner → (ℤ × ℤ),
              factors 0 shift *
                ∏ index : Fin inner, factors index.succ (rest index) :=
          ENNReal.tsum_prod
            (f := fun shift (rest : Fin inner → (ℤ × ℤ)) =>
              factors 0 shift *
                ∏ index : Fin inner, factors index.succ (rest index))
        _ = ∑' shift, factors 0 shift *
              ∑' rest : Fin inner → (ℤ × ℤ),
                ∏ index : Fin inner, factors index.succ (rest index) := by
          apply tsum_congr
          intro shift
          rw [ENNReal.tsum_mul_left]
        _ = (∑' shift, factors 0 shift) *
              ∑' rest : Fin inner → (ℤ × ℤ),
                ∏ index : Fin inner, factors index.succ (rest index) :=
          ENNReal.tsum_mul_right
        _ = (∑' shift, factors 0 shift) *
              ∏ index : Fin inner, ∑' shift, factors index.succ shift := by
          rw [innerHypothesis (fun index => factors index.succ)]
        _ = ∏ index, ∑' shift, factors index shift := by
          rw [Fin.prod_univ_succ]

end Grad.BoundaryKernelAction
