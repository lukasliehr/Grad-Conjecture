import BKB10BaseComposition

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace

/-- The AE7 exponential displacement cost is submultiplicative along every
nonempty finite tuple.  This keeps the input-mode dependence out of the
majorant without paying the width once per composition step. -/
theorem boundaryCoefficientPhaseCost_sum_le_prod : ∀ {count : ℕ},
    0 < count → (tuple : Fin count → ℤ × ℤ) →
    boundaryCoefficientPhaseCost parameters (∑ index, tuple index) ≤
      ∏ index, boundaryCoefficientPhaseCost parameters (tuple index) := by
  intro count positive tuple
  obtain ⟨inner, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  induction inner with
  | zero =>
      simp only [Fin.sum_univ_one, Fin.prod_univ_one]
      exact le_rfl
  | succ inner ih =>
      rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
      apply (boundaryCoefficientPhaseCost_add_le parameters
        (tuple 0) (∑ index : Fin (inner + 1), tuple index.succ)).trans
      apply mul_le_mul_of_nonneg_left
      · exact ih (Nat.succ_pos inner) (fun index => tuple index.succ)
      · exact boundaryCoefficientPhaseCost_nonnegative parameters (tuple 0)

/-- The two-frequency polynomial weight is subadditive along every nonempty
finite tuple. -/
theorem annularFrequency_sum_le_sum {count : ℕ} (positive : 0 < count)
    (tuple : Fin count → ℤ × ℤ) :
    annularFrequency (∑ index, tuple index).1 (∑ index, tuple index).2 ≤
      ∑ index, annularFrequency (tuple index).1 (tuple index).2 := by
  have firstTriangle :
      |(((∑ index, tuple index).1 : ℤ) : ℝ)| ≤
        ∑ index, |((tuple index).1 : ℝ)| := by
    let projection : (ℤ × ℤ) →+ ℤ :=
      { toFun := Prod.fst
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    rw [show (∑ index, tuple index).1 = ∑ index, (tuple index).1 by
      exact map_sum projection tuple Finset.univ]
    push_cast
    exact Finset.abs_sum_le_sum_abs _ _
  have secondTriangle :
      |(((∑ index, tuple index).2 : ℤ) : ℝ)| ≤
        ∑ index, |((tuple index).2 : ℝ)| := by
    let projection : (ℤ × ℤ) →+ ℤ :=
      { toFun := Prod.snd
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    rw [show (∑ index, tuple index).2 = ∑ index, (tuple index).2 by
      exact map_sum projection tuple Finset.univ]
    push_cast
    exact Finset.abs_sum_le_sum_abs _ _
  have oneLe : (1 : ℝ) ≤ ∑ _index : Fin count, (1 : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    exact_mod_cast positive
  unfold annularFrequency
  rw [show (∑ index : Fin count,
      (1 + |((tuple index).1 : ℝ)| + |((tuple index).2 : ℝ)|)) =
      (∑ _index : Fin count, (1 : ℝ)) +
        ∑ index, |((tuple index).1 : ℝ)| +
        ∑ index, |((tuple index).2 : ℝ)| by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]]
  linarith

/-- The direct finite-word max estimate.  Its constant is polynomial in the
word length, unlike iteration of the binary two-term estimate. -/
theorem annularFrequency_sum_pow_le {count : ℕ} (positive : 0 < count)
    (moment : ℕ) (tuple : Fin count → ℤ × ℤ) :
    annularFrequency (∑ index, tuple index).1 (∑ index, tuple index).2 ^ moment ≤
      (count : ℝ) ^ moment *
        ∑ index, annularFrequency (tuple index).1 (tuple index).2 ^ moment := by
  obtain ⟨largest, -, largestBound⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin count))
    (fun index => annularFrequency (tuple index).1 (tuple index).2)
    ⟨⟨0, positive⟩, Finset.mem_univ _⟩
  have sumLe :
      (∑ index, annularFrequency (tuple index).1 (tuple index).2) ≤
        (count : ℝ) * annularFrequency (tuple largest).1 (tuple largest).2 := by
    have cardBound := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin count))
      (fun index => annularFrequency (tuple index).1 (tuple index).2)
      (annularFrequency (tuple largest).1 (tuple largest).2)
      (fun index memberIndex => largestBound index memberIndex)
    rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at cardBound
    exact cardBound
  have baseLe := (annularFrequency_sum_le_sum positive tuple).trans sumLe
  calc
    annularFrequency (∑ index, tuple index).1
          (∑ index, tuple index).2 ^ moment ≤
        ((count : ℝ) *
          annularFrequency (tuple largest).1 (tuple largest).2) ^ moment :=
      pow_le_pow_left₀ (annularFrequency_pos _).le baseLe moment
    _ = (count : ℝ) ^ moment *
        annularFrequency (tuple largest).1 (tuple largest).2 ^ moment := by
      rw [mul_pow]
    _ ≤ (count : ℝ) ^ moment *
        ∑ index, annularFrequency (tuple index).1 (tuple index).2 ^ moment := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg count) moment)
      exact Finset.single_le_sum
        (fun index _ => pow_nonneg (annularFrequency_pos _).le moment)
        (Finset.mem_univ largest)

/-- The exact AE7 tuple weight bound: one factor carries the positive
polynomial moment and every other factor carries only the base moment. -/
theorem fullKernelTupleWeight_le {count : ℕ} (positive : 0 < count)
    (moment : ℕ) (tuple : Fin count → ℤ × ℤ) :
    boundaryCoefficientPhaseCost parameters (∑ index, tuple index) *
        annularFrequency (∑ index, tuple index).1
          (∑ index, tuple index).2 ^ moment ≤
      (count : ℝ) ^ moment * ∑ pivot,
        (boundaryCoefficientPhaseCost parameters (tuple pivot) *
            annularFrequency (tuple pivot).1 (tuple pivot).2 ^ moment *
          ∏ other ∈ Finset.univ.erase pivot,
            boundaryCoefficientPhaseCost parameters (tuple other)) := by
  have phaseBound := boundaryCoefficientPhaseCost_sum_le_prod
    (parameters := parameters) positive tuple
  have frequencyBound := annularFrequency_sum_pow_le positive moment tuple
  have productNonnegative :
      0 ≤ ∏ index, boundaryCoefficientPhaseCost parameters (tuple index) :=
    Finset.prod_nonneg (fun index _ =>
      boundaryCoefficientPhaseCost_nonnegative parameters (tuple index))
  calc
    boundaryCoefficientPhaseCost parameters (∑ index, tuple index) *
        annularFrequency (∑ index, tuple index).1
          (∑ index, tuple index).2 ^ moment ≤
      (∏ index, boundaryCoefficientPhaseCost parameters (tuple index)) *
        ((count : ℝ) ^ moment *
          ∑ pivot, annularFrequency (tuple pivot).1 (tuple pivot).2 ^ moment) :=
      mul_le_mul phaseBound frequencyBound
        (pow_nonneg (annularFrequency_pos _).le _) productNonnegative
    _ = (count : ℝ) ^ moment * ∑ pivot,
        (boundaryCoefficientPhaseCost parameters (tuple pivot) *
            annularFrequency (tuple pivot).1 (tuple pivot).2 ^ moment *
          ∏ other ∈ Finset.univ.erase pivot,
            boundaryCoefficientPhaseCost parameters (tuple other)) := by
      rw [show (∏ index, boundaryCoefficientPhaseCost parameters (tuple index)) *
          ((count : ℝ) ^ moment *
            ∑ pivot, annularFrequency (tuple pivot).1 (tuple pivot).2 ^ moment) =
          (count : ℝ) ^ moment * ∑ pivot,
            ((∏ index, boundaryCoefficientPhaseCost parameters (tuple index)) *
              annularFrequency (tuple pivot).1 (tuple pivot).2 ^ moment) by
            calc
              (∏ index, boundaryCoefficientPhaseCost parameters (tuple index)) *
                    ((count : ℝ) ^ moment * ∑ pivot,
                      annularFrequency (tuple pivot).1 (tuple pivot).2 ^ moment) =
                  (∏ index, boundaryCoefficientPhaseCost parameters (tuple index)) *
                    ∑ pivot, ((count : ℝ) ^ moment *
                      annularFrequency (tuple pivot).1 (tuple pivot).2 ^ moment) := by
                    rw [Finset.mul_sum]
              _ = _ := by
                rw [Finset.mul_sum, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro pivot _
                ring,
        Finset.sum_congr rfl]
      intro pivot _
      rw [← Finset.mul_prod_erase Finset.univ
        (fun index => boundaryCoefficientPhaseCost parameters (tuple index))
        (Finset.mem_univ pivot)]
      ring

end Grad.BoundaryKernelAction
