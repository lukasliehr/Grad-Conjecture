import BKB12TwoFrequencyWords

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal

namespace Grad.BoundaryKernelAction

open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace

private theorem bkbOfRealFinsetProd {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (nonnegative : ∀ index ∈ s, 0 ≤ f index) :
    ENNReal.ofReal (∏ index ∈ s, f index) =
      ∏ index ∈ s, ENNReal.ofReal (f index) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert element others outside ih =>
      rw [Finset.prod_insert outside, Finset.prod_insert outside,
        ENNReal.ofReal_mul (nonnegative element (Finset.mem_insert_self _ _)),
        ih (fun index memberIndex =>
          nonnegative index (Finset.mem_insert_of_mem memberIndex))]

private theorem bkbEnnTsumFinsetSum {valueType indexType : Type*}
    (s : Finset indexType) (f : indexType → valueType → ℝ≥0∞) :
    (∑' value, ∑ index ∈ s, f index value) =
      ∑ index ∈ s, ∑' value, f index value := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert element others outside ih =>
      rw [tsum_congr (fun value => Finset.sum_insert outside),
        Summable.tsum_add ENNReal.summable ENNReal.summable, ih,
        Finset.sum_insert outside]

/-- Extended-real form of the exact AE7 displacement weight. -/
def ennFullKernelWeight (parameters : PhaseParameters) (moment : ℕ)
    (shift : ℤ × ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (boundaryCoefficientPhaseCost parameters shift *
    annularFrequency shift.1 shift.2 ^ moment)

theorem ennFullKernelWeight_tuple_le {count : ℕ} (positive : 0 < count)
    (moment : ℕ) (tuple : Fin count → ℤ × ℤ) :
    ennFullKernelWeight parameters moment (∑ index, tuple index) ≤
      ENNReal.ofReal ((count : ℝ) ^ moment) * ∑ pivot,
        (ennFullKernelWeight parameters moment (tuple pivot) *
          ∏ other ∈ Finset.univ.erase pivot,
            ennFullKernelWeight parameters 0 (tuple other)) := by
  have realBound := fullKernelTupleWeight_le
    (parameters := parameters) positive moment tuple
  calc
    ennFullKernelWeight parameters moment (∑ index, tuple index) ≤
        ENNReal.ofReal ((count : ℝ) ^ moment * ∑ pivot,
          (boundaryCoefficientPhaseCost parameters (tuple pivot) *
              annularFrequency (tuple pivot).1 (tuple pivot).2 ^ moment *
            ∏ other ∈ Finset.univ.erase pivot,
              boundaryCoefficientPhaseCost parameters (tuple other))) :=
      ENNReal.ofReal_le_ofReal realBound
    _ = ENNReal.ofReal ((count : ℝ) ^ moment) * ∑ pivot,
        (ennFullKernelWeight parameters moment (tuple pivot) *
          ∏ other ∈ Finset.univ.erase pivot,
            ennFullKernelWeight parameters 0 (tuple other)) := by
      rw [ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg count) moment),
        ENNReal.ofReal_sum_of_nonneg]
      · congr 1
        apply Finset.sum_congr rfl
        intro pivot _
        rw [ENNReal.ofReal_mul
            (mul_nonneg
              (boundaryCoefficientPhaseCost_nonnegative parameters (tuple pivot))
              (pow_nonneg (annularFrequency_pos _).le moment)),
          ENNReal.ofReal_mul
            (boundaryCoefficientPhaseCost_nonnegative parameters (tuple pivot)),
          bkbOfRealFinsetProd _ _]
        · unfold ennFullKernelWeight
          simp only [pow_zero, mul_one,
            ENNReal.ofReal_mul
              (boundaryCoefficientPhaseCost_nonnegative parameters (tuple pivot))]
        · intro other memberOther
          exact boundaryCoefficientPhaseCost_nonnegative parameters (tuple other)
      · intro pivot _
        exact mul_nonneg
          (mul_nonneg
            (boundaryCoefficientPhaseCost_nonnegative parameters (tuple pivot))
            (pow_nonneg (annularFrequency_pos _).le moment))
          (Finset.prod_nonneg (fun other _ =>
            boundaryCoefficientPhaseCost_nonnegative parameters (tuple other)))

/-- Extended weighted mass of a scalar two-frequency word. -/
def ennTwoFrequencyWordMass {count : ℕ} (parameters : PhaseParameters)
    (moment : ℕ)
    (factors : Fin (count + 1) → (ℤ × ℤ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' total, ennFullKernelWeight parameters moment total *
    twoFrequencyScalarWord factors total

/-- The direct word estimate.  Exactly one factor bears the positive moment;
the remaining factors bear only moment zero. -/
theorem ennTwoFrequencyWordMass_le {count : ℕ}
    (parameters : PhaseParameters) (moment : ℕ)
    (factors : Fin (count + 1) → (ℤ × ℤ) → ℝ≥0∞) :
    ennTwoFrequencyWordMass parameters moment factors ≤
      ENNReal.ofReal (((count : ℝ) + 1) ^ moment) * ∑ pivot,
        ((∑' shift, ennFullKernelWeight parameters moment shift *
            factors pivot shift) *
          ∏ other ∈ Finset.univ.erase pivot,
            ∑' shift, ennFullKernelWeight parameters 0 shift *
              factors other shift) := by
  calc
    ennTwoFrequencyWordMass parameters moment factors =
        ∑' tuple : Fin (count + 1) → (ℤ × ℤ),
          ennFullKernelWeight parameters moment (∑ index, tuple index) *
            ∏ index, factors index (tuple index) :=
      twoFrequencyScalarWord_weighted factors
        (ennFullKernelWeight parameters moment)
    _ ≤ ∑' tuple : Fin (count + 1) → (ℤ × ℤ),
        (ENNReal.ofReal (((count : ℝ) + 1) ^ moment) * ∑ pivot,
          (ennFullKernelWeight parameters moment (tuple pivot) *
            ∏ other ∈ Finset.univ.erase pivot,
              ennFullKernelWeight parameters 0 (tuple other))) *
          ∏ index, factors index (tuple index) := by
      apply ENNReal.tsum_le_tsum
      intro tuple
      have bound := ennFullKernelWeight_tuple_le
        (parameters := parameters) (Nat.succ_pos count) moment tuple
      exact mul_le_mul'
        (by simpa only [Nat.cast_succ] using bound) le_rfl
    _ = ENNReal.ofReal (((count : ℝ) + 1) ^ moment) * ∑ pivot,
        ∑' tuple : Fin (count + 1) → (ℤ × ℤ),
          ((ennFullKernelWeight parameters moment (tuple pivot) *
            ∏ other ∈ Finset.univ.erase pivot,
              ennFullKernelWeight parameters 0 (tuple other)) *
            ∏ index, factors index (tuple index)) := by
      rw [show (fun tuple : Fin (count + 1) → (ℤ × ℤ) =>
          (ENNReal.ofReal (((count : ℝ) + 1) ^ moment) * ∑ pivot,
            (ennFullKernelWeight parameters moment (tuple pivot) *
              ∏ other ∈ Finset.univ.erase pivot,
                ennFullKernelWeight parameters 0 (tuple other))) *
            ∏ index, factors index (tuple index)) =
          fun tuple => ENNReal.ofReal (((count : ℝ) + 1) ^ moment) *
            ∑ pivot,
              ((ennFullKernelWeight parameters moment (tuple pivot) *
                ∏ other ∈ Finset.univ.erase pivot,
                  ennFullKernelWeight parameters 0 (tuple other)) *
                ∏ index, factors index (tuple index)) from
          funext (fun tuple => by rw [mul_assoc, Finset.sum_mul])]
      rw [ENNReal.tsum_mul_left]
      apply congrArg
      exact bkbEnnTsumFinsetSum _ _
    _ = ENNReal.ofReal (((count : ℝ) + 1) ^ moment) * ∑ pivot,
        ((∑' shift, ennFullKernelWeight parameters moment shift *
            factors pivot shift) *
          ∏ other ∈ Finset.univ.erase pivot,
            ∑' shift, ennFullKernelWeight parameters 0 shift *
              factors other shift) := by
      apply congrArg
      apply Finset.sum_congr rfl
      intro pivot _
      calc
        (∑' tuple : Fin (count + 1) → (ℤ × ℤ),
            ((ennFullKernelWeight parameters moment (tuple pivot) *
              ∏ other ∈ Finset.univ.erase pivot,
                ennFullKernelWeight parameters 0 (tuple other)) *
              ∏ index, factors index (tuple index))) =
            ∑' tuple : Fin (count + 1) → (ℤ × ℤ),
              ∏ index,
                ((if index = pivot
                  then ennFullKernelWeight parameters moment (tuple index)
                  else ennFullKernelWeight parameters 0 (tuple index)) *
                  factors index (tuple index)) := by
          apply tsum_congr
          intro tuple
          calc
            (ennFullKernelWeight parameters moment (tuple pivot) *
                  ∏ other ∈ Finset.univ.erase pivot,
                    ennFullKernelWeight parameters 0 (tuple other)) *
                ∏ index, factors index (tuple index) =
                (ennFullKernelWeight parameters moment (tuple pivot) *
                  factors pivot (tuple pivot)) *
                  ((∏ other ∈ Finset.univ.erase pivot,
                    ennFullKernelWeight parameters 0 (tuple other)) *
                    ∏ other ∈ Finset.univ.erase pivot,
                      factors other (tuple other)) := by
              rw [← Finset.mul_prod_erase Finset.univ
                (fun index => factors index (tuple index))
                (Finset.mem_univ pivot)]
              ring
            _ = (ennFullKernelWeight parameters moment (tuple pivot) *
                  factors pivot (tuple pivot)) *
                ∏ other ∈ Finset.univ.erase pivot,
                  (ennFullKernelWeight parameters 0 (tuple other) *
                    factors other (tuple other)) := by
              rw [← Finset.prod_mul_distrib]
            _ = ∏ index,
                ((if index = pivot
                  then ennFullKernelWeight parameters moment (tuple index)
                  else ennFullKernelWeight parameters 0 (tuple index)) *
                  factors index (tuple index)) := by
              rw [← Finset.mul_prod_erase Finset.univ
                (fun index =>
                  ((if index = pivot
                    then ennFullKernelWeight parameters moment (tuple index)
                    else ennFullKernelWeight parameters 0 (tuple index)) *
                    factors index (tuple index)))
                (Finset.mem_univ pivot), if_pos rfl]
              apply congrArg
              apply Finset.prod_congr rfl
              intro other memberOther
              rw [if_neg (Finset.mem_erase.mp memberOther).1]
        _ = ∏ index, ∑' shift,
              ((if index = pivot
                then ennFullKernelWeight parameters moment shift
                else ennFullKernelWeight parameters 0 shift) *
                factors index shift) :=
          twoFrequencyTuple_tsum_prod
            (fun index shift =>
              ((if index = pivot
                then ennFullKernelWeight parameters moment shift
                else ennFullKernelWeight parameters 0 shift) *
                factors index shift))
        _ = (∑' shift, ennFullKernelWeight parameters moment shift *
              factors pivot shift) *
            ∏ other ∈ Finset.univ.erase pivot,
              ∑' shift, ennFullKernelWeight parameters 0 shift *
                factors other shift := by
          rw [← Finset.mul_prod_erase Finset.univ
            (fun index => ∑' shift,
              ((if index = pivot
                then ennFullKernelWeight parameters moment shift
                else ennFullKernelWeight parameters 0 shift) *
                factors index shift))
            (Finset.mem_univ pivot)]
          apply congrArg₂
          · apply tsum_congr
            intro shift
            rw [if_pos rfl]
          · apply Finset.prod_congr rfl
            intro other memberOther
            apply tsum_congr
            intro shift
            rw [if_neg (Finset.mem_erase.mp memberOther).1]

end Grad.BoundaryKernelAction
