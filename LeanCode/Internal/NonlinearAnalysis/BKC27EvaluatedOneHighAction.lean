import BKC26CovariantPhysicalMoments

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation

theorem UniformKernelMoments.oneHigh_bound {Index : Type*}
    {parameters : PhaseParameters} {input output : ℕ}
    {size : Index → ℕ → ℝ} (sizeNonnegative : ∀ state moment, 0 ≤ size state moment)
    {family : Index → FullTwoFrequencyKernel parameters input output}
    (bounded : UniformKernelMoments parameters size family) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ state (high : NegativeTotalTrace parameters grade input)
        (low : NegativeTotalTrace parameters 0 input),
        ‖fullOneHighKernelAction parameters grade (family state) high low‖ ≤
          constant * (size state 1 * ‖high‖ + size state (grade + 1) * ‖low‖) := by
  obtain ⟨lowConstant, lowNonnegative, lowBound⟩ := bounded 1
  obtain ⟨highConstant, highNonnegative, highBound⟩ := bounded (grade + 1)
  refine ⟨2 ^ grade * (lowConstant + highConstant), by positivity, ?_⟩
  intro state high low
  have lowSizeNonnegative := sizeNonnegative state 1
  have highSizeNonnegative := sizeNonnegative state (grade + 1)
  apply (fullOneHighKernelAction_bound parameters grade (family state) high low).trans
  calc
    _ ≤ 2 ^ grade *
      ((lowConstant * size state 1) * ‖high‖ +
        (highConstant * size state (grade + 1)) * ‖low‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul_of_nonneg_right (lowBound state) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (highBound state) (norm_nonneg _))
    _ ≤ 2 ^ grade *
      (((lowConstant + highConstant) * size state 1) * ‖high‖ +
        ((lowConstant + highConstant) * size state (grade + 1)) * ‖low‖) := by
      gcongr <;> linarith
    _ = _ := by ring

/-- AH20 at the total trace grade used in AH19. The carrier is the original
seven scalar weighted square sums. -/
abbrev SevenSlotTotalTrace (parameters : PhaseParameters) (grade : ℕ) :=
  PiLp 2 (fun _ : Fin 7 => NegativeTotalTrace parameters grade 1)

theorem sevenSlotFlatten_total_compatible (parameters : PhaseParameters) (grade : ℕ)
    (high : SevenSlotTotalTrace parameters grade) (low : SevenSlotTotalTrace parameters 0)
    (compatible : ∀ slot, TotalTraceCompatible parameters grade (high slot) (low slot)) :
    TotalTraceCompatible parameters grade
      (sevenSlotFlatten parameters grade 0 high) (sevenSlotFlatten parameters 0 0 low) := by
  intro mode
  apply PiLp.ext
  intro slot
  exact congrArg (fun value : ComplexEuclidean 1 => value 0) (compatible slot mode)

/-- Evaluated AH19 bound for the actual covariant reconstruction. The state
factor is B(t+8), reflecting precisely the +1 moment in the negative-half
trace estimate; the high-input coefficient uses the fixed finite B8 size. -/
theorem actualCovariantKernel_oneHigh_bound
    (parameters : PhaseParameters) (L compactRadius : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : BoundaryReconstructionState parameters L compactRadius)
        (high : SevenSlotTotalTrace parameters grade) (low : SevenSlotTotalTrace parameters 0),
      ‖fullOneHighKernelAction parameters grade
        (actualCovariantKernel parameters L state.rho state.alpha state.delta state.parameter
          state.epsilon compactRadius state.field state.small state.compactNonnegative
          state.alphaSmall state.deltaSmall state.parameterSmall)
        (sevenSlotFlatten parameters grade 0 high) (sevenSlotFlatten parameters 0 0 low)‖ ≤
      constant *
        ((1 + physicalBudget parameters state.field state.rho state.epsilon 8) * ‖high‖ +
          (1 + physicalBudget parameters state.field state.rho state.epsilon (grade + 8)) * ‖low‖) := by
  obtain ⟨constant, nonnegative, bound⟩ :=
    (actualCovariantKernel_physicalMoments parameters L compactRadius).oneHigh_bound
      BoundaryReconstructionState.size_nonnegative grade
  refine ⟨constant, nonnegative, ?_⟩
  intro state high low
  simpa only [BoundaryReconstructionState.size, sevenSlotFlatten_norm, Nat.reduceAdd,
    Nat.add_assoc] using bound state
      (sevenSlotFlatten parameters grade 0 high) (sevenSlotFlatten parameters 0 0 low)

theorem actualRotatedCovariantKernel_oneHigh_bound
    (parameters : PhaseParameters) (L compactRadius : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : BoundaryReconstructionState parameters L compactRadius)
        (high : SevenSlotTotalTrace parameters grade) (low : SevenSlotTotalTrace parameters 0),
      ‖fullOneHighKernelAction parameters grade
        (actualRotatedCovariantKernel parameters L state.rho state.alpha state.delta state.parameter
          state.epsilon compactRadius state.field state.small state.compactNonnegative
          state.alphaSmall state.deltaSmall state.parameterSmall)
        (sevenSlotFlatten parameters grade 0 high) (sevenSlotFlatten parameters 0 0 low)‖ ≤
      constant *
        ((1 + physicalBudget parameters state.field state.rho state.epsilon 8) * ‖high‖ +
          (1 + physicalBudget parameters state.field state.rho state.epsilon (grade + 8)) * ‖low‖) := by
  obtain ⟨constant, nonnegative, bound⟩ :=
    (actualRotatedCovariantKernel_physicalMoments parameters L compactRadius).oneHigh_bound
      BoundaryReconstructionState.size_nonnegative grade
  refine ⟨constant, nonnegative, ?_⟩
  intro state high low
  simpa only [BoundaryReconstructionState.size, sevenSlotFlatten_norm, Nat.reduceAdd,
    Nat.add_assoc] using bound state
      (sevenSlotFlatten parameters grade 0 high) (sevenSlotFlatten parameters 0 0 low)

end Grad.BoundaryKernelAction
