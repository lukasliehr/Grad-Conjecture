import BKB20KernelPowerAlgebra

noncomputable section

set_option maxHeartbeats 2400000

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

private abbrev KernelShift := ℤ × ℤ

theorem fullKernelTailPairSummable_left {dimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) (total input : KernelShift) :
    Summable (fun pair : ℕ × KernelShift =>
      ‖(kernel.entry (total - pair.2) (input + pair.2)).comp
        ((fullKernelPower kernel pair.1).entry pair.2 input)‖) := by
  have lowNonnegative :=
    (fullKernelMoment_nonnegative parameters 0 kernel).trans lowBound
  have scalarSummable : Summable (fun exponent : ℕ =>
      ((exponent : ℝ) + 1) ^ (0 + 1) * low ^ exponent *
        fullKernelMoment parameters 0 kernel) :=
    (fullKernelNeumannMajorant_summable 0 low lowNonnegative lowSmall).mul_right _
  have shiftedKernel : Summable (fun shift : KernelShift =>
      kernel.entryNorm (total - shift)) :=
    ((Equiv.subLeft total).summable_iff
      (f := fun shift : KernelShift => kernel.entryNorm shift)).mpr
      (fullKernelEntryNorm_summable parameters kernel)
  have marginals := scalarSummable.mul_of_nonneg shiftedKernel
    (fun exponent => mul_nonneg
      (mul_nonneg (pow_nonneg (by positivity) (0 + 1))
        (pow_nonneg lowNonnegative exponent))
      (fullKernelMoment_nonnegative parameters 0 kernel))
    (fun shift => fullKernelEntryNorm_nonnegative kernel (total - shift))
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun pair => ?_)
    marginals
  have powerEntryBound :
      ‖(fullKernelPower kernel pair.1).entry pair.2 input‖ ≤
        ((pair.1 : ℝ) + 1) ^ (0 + 1) * low ^ pair.1 *
          fullKernelMoment parameters 0 kernel :=
    ((fullKernelPower kernel pair.1).entry_le pair.2 input).trans
      ((fullKernelMoment_entryNorm_le parameters
        (fullKernelPower kernel pair.1) pair.2).trans
        (fullKernelPower_theta_moment_le parameters 0 pair.1 kernel low lowBound))
  calc
    ‖(kernel.entry (total - pair.2) (input + pair.2)).comp
        ((fullKernelPower kernel pair.1).entry pair.2 input)‖ ≤
        ‖kernel.entry (total - pair.2) (input + pair.2)‖ *
          ‖(fullKernelPower kernel pair.1).entry pair.2 input‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ kernel.entryNorm (total - pair.2) *
          (((pair.1 : ℝ) + 1) ^ (0 + 1) * low ^ pair.1 *
            fullKernelMoment parameters 0 kernel) := by
      exact mul_le_mul
        (kernel.entry_le (total - pair.2) (input + pair.2)) powerEntryBound
        (norm_nonneg _) (fullKernelEntryNorm_nonnegative kernel _)
    _ = ((pair.1 : ℝ) + 1) ^ (0 + 1) * low ^ pair.1 *
          fullKernelMoment parameters 0 kernel *
            kernel.entryNorm (total - pair.2) := by ring

theorem fullKernelTailPairSummable_right {dimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) (total input : KernelShift) :
    Summable (fun pair : ℕ × KernelShift =>
      ‖((fullKernelPower kernel pair.1).entry
          (total - pair.2) (input + pair.2)).comp
        (kernel.entry pair.2 input)‖) := by
  have lowNonnegative :=
    (fullKernelMoment_nonnegative parameters 0 kernel).trans lowBound
  have scalarSummable : Summable (fun exponent : ℕ =>
      ((exponent : ℝ) + 1) ^ (0 + 1) * low ^ exponent *
        fullKernelMoment parameters 0 kernel) :=
    (fullKernelNeumannMajorant_summable 0 low lowNonnegative lowSmall).mul_right _
  have kernelSummable := fullKernelEntryNorm_summable parameters kernel
  have marginals := scalarSummable.mul_of_nonneg kernelSummable
    (fun exponent => mul_nonneg
      (mul_nonneg (pow_nonneg (by positivity) (0 + 1))
        (pow_nonneg lowNonnegative exponent))
      (fullKernelMoment_nonnegative parameters 0 kernel))
    (fullKernelEntryNorm_nonnegative kernel)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun pair => ?_)
    marginals
  have powerEntryBound :
      ‖(fullKernelPower kernel pair.1).entry
          (total - pair.2) (input + pair.2)‖ ≤
        ((pair.1 : ℝ) + 1) ^ (0 + 1) * low ^ pair.1 *
          fullKernelMoment parameters 0 kernel :=
    ((fullKernelPower kernel pair.1).entry_le (total - pair.2)
      (input + pair.2)).trans
      ((fullKernelMoment_entryNorm_le parameters
        (fullKernelPower kernel pair.1) (total - pair.2)).trans
        (fullKernelPower_theta_moment_le parameters 0 pair.1 kernel low lowBound))
  calc
    ‖((fullKernelPower kernel pair.1).entry
          (total - pair.2) (input + pair.2)).comp
        (kernel.entry pair.2 input)‖ ≤
        ‖(fullKernelPower kernel pair.1).entry
          (total - pair.2) (input + pair.2)‖ *
            ‖kernel.entry pair.2 input‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (((pair.1 : ℝ) + 1) ^ (0 + 1) * low ^ pair.1 *
          fullKernelMoment parameters 0 kernel) * kernel.entryNorm pair.2 := by
      exact mul_le_mul powerEntryBound (kernel.entry_le pair.2 input)
        (norm_nonneg _)
        (mul_nonneg
          (mul_nonneg (pow_nonneg (by positivity) (0 + 1))
            (pow_nonneg lowNonnegative pair.1))
          (fullKernelMoment_nonnegative parameters 0 kernel))

/-- The left kernel product with the strict Neumann tail removes its first
power. -/
theorem fullKernel_comp_neumannTail {dimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) :
    fullKernelComposition kernel
        (fullKernelNeumannTail parameters kernel low lowBound lowSmall) =
      fullKernelSub
        (fullKernelNeumannTail parameters kernel low lowBound lowSmall) kernel := by
  apply FullTwoFrequencyKernel.ext_entry
  intro total input
  rw [fullKernelComposition_entry, fullKernelSub_entry,
    fullKernelNeumannTail_entry]
  have powerSummable := fullKernelPower_entry_summable parameters kernel low
    lowBound lowSmall
  calc
    (∑' shift : KernelShift,
        (kernel.entry (total - shift) (input + shift)).comp
          (∑' exponent : ℕ,
            (fullKernelPower kernel exponent).entry shift input)) =
        ∑' shift : KernelShift, ∑' exponent : ℕ,
          (kernel.entry (total - shift) (input + shift)).comp
            ((fullKernelPower kernel exponent).entry shift input) := by
      apply tsum_congr
      intro shift
      let composeLeft :=
        (ContinuousLinearMap.compL ℂ
          (ComplexEuclidean dimension) (ComplexEuclidean dimension)
            (ComplexEuclidean dimension))
          (kernel.entry (total - shift) (input + shift))
      change composeLeft (∑' exponent : ℕ,
          (fullKernelPower kernel exponent).entry shift input) = _
      exact composeLeft.map_tsum (powerSummable shift input)
    _ = ∑' exponent : ℕ, ∑' shift : KernelShift,
          (kernel.entry (total - shift) (input + shift)).comp
            ((fullKernelPower kernel exponent).entry shift input) :=
      Summable.tsum_comm (by
        apply (Summable.of_norm
          (fullKernelTailPairSummable_left parameters kernel low lowBound
            lowSmall total input)).congr
        intro pair
        rfl)
    _ = ∑' exponent : ℕ,
          (fullKernelPower kernel (exponent + 1)).entry total input := by
      apply tsum_congr
      intro exponent
      rw [← fullKernelComposition_entry]
      exact congrArg (fun power => power.entry total input)
        (fullKernelPower_succ_left kernel exponent).symm
    _ = (fullKernelNeumannTail parameters kernel low lowBound lowSmall).entry
          total input - kernel.entry total input :=
      fullKernelPower_shift_tsum_eq_tail_sub parameters kernel low lowBound
        lowSmall total input

/-- The right kernel product with the strict Neumann tail removes its first
power. -/
theorem fullKernelNeumannTail_comp {dimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) :
    fullKernelComposition
        (fullKernelNeumannTail parameters kernel low lowBound lowSmall) kernel =
      fullKernelSub
        (fullKernelNeumannTail parameters kernel low lowBound lowSmall) kernel := by
  apply FullTwoFrequencyKernel.ext_entry
  intro total input
  rw [fullKernelComposition_entry, fullKernelSub_entry]
  have powerSummable := fullKernelPower_entry_summable parameters kernel low
    lowBound lowSmall
  calc
    (∑' shift : KernelShift,
        ((fullKernelNeumannTail parameters kernel low lowBound lowSmall).entry
          (total - shift) (input + shift)).comp (kernel.entry shift input)) =
        ∑' shift : KernelShift, ∑' exponent : ℕ,
          ((fullKernelPower kernel exponent).entry
            (total - shift) (input + shift)).comp (kernel.entry shift input) := by
      apply tsum_congr
      intro shift
      rw [fullKernelNeumannTail_entry]
      let composition := ContinuousLinearMap.compL ℂ
        (ComplexEuclidean dimension) (ComplexEuclidean dimension)
          (ComplexEuclidean dimension)
      let composeRight :=
        (ContinuousLinearMap.apply ℂ
          (ComplexEuclidean dimension →L[ℂ] ComplexEuclidean dimension)
          (kernel.entry shift input)).comp composition
      change composeRight (∑' exponent : ℕ,
          (fullKernelPower kernel exponent).entry
            (total - shift) (input + shift)) = _
      exact composeRight.map_tsum (powerSummable (total - shift) (input + shift))
    _ = ∑' exponent : ℕ, ∑' shift : KernelShift,
          ((fullKernelPower kernel exponent).entry
            (total - shift) (input + shift)).comp (kernel.entry shift input) :=
      Summable.tsum_comm (by
        apply (Summable.of_norm
          (fullKernelTailPairSummable_right parameters kernel low lowBound
            lowSmall total input)).congr
        intro pair
        rfl)
    _ = ∑' exponent : ℕ,
          (fullKernelPower kernel (exponent + 1)).entry total input := by
      apply tsum_congr
      intro exponent
      rw [← fullKernelComposition_entry]
      rfl
    _ = (fullKernelNeumannTail parameters kernel low lowBound lowSmall).entry
          total input - kernel.entry total input :=
      fullKernelPower_shift_tsum_eq_tail_sub parameters kernel low lowBound
        lowSmall total input

end Grad.BoundaryKernelAction
