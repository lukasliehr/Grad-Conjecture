import BKB14KernelPowers

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal

namespace Grad.BoundaryKernelAction

open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace

theorem ennFullKernelMoment_eq {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (moment : ℕ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension) :
    (∑' shift : ℤ × ℤ,
      ennFullKernelWeight parameters moment shift *
        ENNReal.ofReal (kernel.entryNorm shift)) =
      ENNReal.ofReal (fullKernelMoment parameters moment kernel) := by
  rw [fullKernelMoment,
    ENNReal.ofReal_tsum_of_nonneg
      (fun shift => mul_nonneg
        (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift)
          (pow_nonneg (annularFrequency_pos shift).le moment))
        (fullKernelEntryNorm_nonnegative kernel shift))
      (kernel.moments moment)]
  apply tsum_congr
  intro shift
  unfold ennFullKernelWeight
  rw [← ENNReal.ofReal_mul
    (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift)
      (pow_nonneg (annularFrequency_pos shift).le moment))]

private theorem bkb15OfRealFinsetProd {ι : Type*} (s : Finset ι) (f : ι → ℝ)
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

/-- Direct K4 bound for a full input-mode-dependent kernel word.  This is the
unsimplified one-high formula, with one positive moment and all other factors
at moment zero. -/
theorem fullKernelPower_moment_le_sum {dimension : ℕ}
    (parameters : PhaseParameters) (moment exponent : ℕ)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension) :
    fullKernelMoment parameters moment (fullKernelPower kernel exponent) ≤
      ((exponent : ℝ) + 1) ^ moment * ∑ _pivot : Fin (exponent + 1),
        (fullKernelMoment parameters moment kernel *
          ∏ _other ∈ Finset.univ.erase _pivot,
            fullKernelMoment parameters 0 kernel) := by
  let factors : Fin (exponent + 1) → (ℤ × ℤ) → ℝ≥0∞ :=
    fun _ shift => ENNReal.ofReal (kernel.entryNorm shift)
  have wordBound := ennTwoFrequencyWordMass_le parameters moment factors
  have powerToWord :
      ENNReal.ofReal
          (fullKernelMoment parameters moment (fullKernelPower kernel exponent)) ≤
        ennTwoFrequencyWordMass parameters moment factors := by
    rw [← ennFullKernelMoment_eq parameters moment
      (fullKernelPower kernel exponent)]
    unfold ennTwoFrequencyWordMass
    apply ENNReal.tsum_le_tsum
    intro total
    exact mul_le_mul' le_rfl
      (fullKernelPower_entryNorm_enorm_le kernel exponent total)
  have momentNonnegative := fullKernelMoment_nonnegative parameters moment kernel
  have zeroNonnegative := fullKernelMoment_nonnegative parameters 0 kernel
  have rightNonnegative :
      0 ≤ ((exponent : ℝ) + 1) ^ moment *
          ∑ pivot : Fin (exponent + 1),
            (fullKernelMoment parameters moment kernel *
              ∏ other ∈ Finset.univ.erase pivot,
                fullKernelMoment parameters 0 kernel) := by
    positivity
  have encodedRight :
      ENNReal.ofReal (((exponent : ℝ) + 1) ^ moment *
          ∑ pivot : Fin (exponent + 1),
            (fullKernelMoment parameters moment kernel *
              ∏ other ∈ Finset.univ.erase pivot,
                fullKernelMoment parameters 0 kernel)) =
        ENNReal.ofReal (((exponent : ℝ) + 1) ^ moment) * ∑ pivot,
          ((∑' shift, ennFullKernelWeight parameters moment shift *
              factors pivot shift) *
            ∏ other ∈ Finset.univ.erase pivot,
              ∑' shift, ennFullKernelWeight parameters 0 shift *
                factors other shift) := by
    rw [ENNReal.ofReal_mul (pow_nonneg (by positivity) moment),
      ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      apply Finset.sum_congr rfl
      intro pivot _
      rw [ENNReal.ofReal_mul momentNonnegative,
        bkb15OfRealFinsetProd _ _]
      · unfold factors
        rw [ennFullKernelMoment_eq parameters moment kernel]
        apply congrArg₂
        · rfl
        · apply Finset.prod_congr rfl
          intro other _
          rw [ennFullKernelMoment_eq parameters 0 kernel]
      · intro other _
        exact zeroNonnegative
    · intro pivot _
      exact mul_nonneg momentNonnegative
        (Finset.prod_nonneg (fun other _ => zeroNonnegative))
  have encodedBound :
      ENNReal.ofReal
          (fullKernelMoment parameters moment (fullKernelPower kernel exponent)) ≤
        ENNReal.ofReal (((exponent : ℝ) + 1) ^ moment *
          ∑ pivot : Fin (exponent + 1),
            (fullKernelMoment parameters moment kernel *
              ∏ other ∈ Finset.univ.erase pivot,
                fullKernelMoment parameters 0 kernel)) := by
    rw [encodedRight]
    exact powerToWord.trans wordBound
  exact (ENNReal.ofReal_le_ofReal_iff rightNonnegative).mp encodedBound

/-- The manuscript K4 polynomial power estimate.  Only the zero moment is
raised to `exponent`; no positive-grade smallness is assumed. -/
theorem fullKernelPower_moment_le {dimension : ℕ}
    (parameters : PhaseParameters) (moment exponent : ℕ)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension) :
    fullKernelMoment parameters moment (fullKernelPower kernel exponent) ≤
      ((exponent : ℝ) + 1) ^ (moment + 1) *
        (fullKernelMoment parameters 0 kernel ^ exponent *
          fullKernelMoment parameters moment kernel) := by
  apply (fullKernelPower_moment_le_sum parameters moment exponent kernel).trans_eq
  have perPivot : ∀ pivot : Fin (exponent + 1),
      fullKernelMoment parameters moment kernel *
          ∏ _other ∈ Finset.univ.erase pivot,
            fullKernelMoment parameters 0 kernel =
        fullKernelMoment parameters moment kernel *
          fullKernelMoment parameters 0 kernel ^ exponent := by
    intro pivot
    rw [Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ pivot),
      Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
  rw [Finset.sum_congr rfl (fun pivot _ => perPivot pivot),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end Grad.BoundaryKernelAction
