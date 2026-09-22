import BCT22PhysicalBoundaryMoments
import BKC27EvaluatedOneHighAction

noncomputable section

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

def PhysicalBoundaryState.of (parameters : PhaseParameters) (L compact rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤ physicalBoundaryLowRadius parameters L compact)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact) :
    PhysicalBoundaryState parameters L compact :=
  ⟨BoundaryReconstructionState.of rho alpha delta parameter epsilon field
    (physicalBoundary_reconstruction_small parameters L rho epsilon compact field small)
    compactNonnegative alphaSmall deltaSmall parameterSmall, small⟩

/-- The concrete physical AH21 kernel, with its B(t+7) moment bound and
constant chosen before all state arguments. -/
theorem actualDifferentiatedPhysicalBoundaryKernel_evaluated
    (parameters : PhaseParameters) (L compact : ℝ) (moment : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
        (small : physicalBudget parameters field rho epsilon 7 ≤ physicalBoundaryLowRadius parameters L compact)
        (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
        (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact),
      fullKernelMoment parameters moment
        (actualDifferentiatedPhysicalBoundaryKernel parameters L rho alpha delta parameter epsilon compact field
          small compactNonnegative alphaSmall deltaSmall parameterSmall) ≤
        constant * (1 + physicalBudget parameters field rho epsilon (moment + 7)) := by
  obtain ⟨constant, nonnegative, bound⟩ :=
    actualDifferentiatedPhysicalBoundaryKernel_uniformMoments parameters L compact moment
  refine ⟨constant, nonnegative, ?_⟩
  intro rho alpha delta parameter epsilon field small compactNonnegative alphaSmall deltaSmall parameterSmall
  exact bound (PhysicalBoundaryState.of parameters L compact rho alpha delta parameter epsilon field
    small compactNonnegative alphaSmall deltaSmall parameterSmall)

/-- AH22 with evaluated state dependence in the exact split P_R norm. -/
theorem actualPhysicalBoundaryPR_uniform_bound
    (parameters : PhaseParameters) (L compact : ℝ) (angular cell : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
        (small : physicalBudget parameters field rho epsilon 7 ≤ physicalBoundaryLowRadius parameters L compact)
        (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
        (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
        (input : SevenSlotTrace parameters angular cell),
      ‖actualPhysicalBoundaryPR parameters L rho alpha delta parameter epsilon compact field
          small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input‖ ≤
        constant * (1 + physicalBudget parameters field rho epsilon (angular + cell + 8)) * ‖input‖ := by
  obtain ⟨constant, nonnegative, bound⟩ :=
    actualDifferentiatedPhysicalBoundaryKernel_evaluated parameters L compact (angular + cell + 1)
  refine ⟨constant, nonnegative, ?_⟩
  intro rho alpha delta parameter epsilon field small compactNonnegative alphaSmall deltaSmall parameterSmall input
  apply (actualPhysicalBoundaryPR_bound parameters L rho alpha delta parameter epsilon compact field
    small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell input).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg input)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    bound rho alpha delta parameter epsilon field small compactNonnegative alphaSmall deltaSmall parameterSmall

/-- AH19/AH21 in the actual total-grade P_R carrier. Exactly one high
physical coefficient B(t+8) is paired with the low trace; B8 is merely
finite on the high-input coefficient, never required to be small. -/
theorem actualTotalPhysicalBoundary_uniform_oneHigh
    (parameters : PhaseParameters) (L compact : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
        (small : physicalBudget parameters field rho epsilon 7 ≤ physicalBoundaryLowRadius parameters L compact)
        (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
        (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
        (high : NegativeTotalTrace parameters grade 7) (low : NegativeTotalTrace parameters 0 7)
        (compatible : TotalTraceCompatible parameters grade high low),
      ‖actualTotalPhysicalBoundary parameters L rho alpha delta parameter epsilon compact field
          small compactNonnegative alphaSmall deltaSmall parameterSmall grade high low compatible‖ ≤
        constant * ((1 + physicalBudget parameters field rho epsilon 8) * ‖high‖ +
          (1 + physicalBudget parameters field rho epsilon (grade + 8)) * ‖low‖) := by
  obtain ⟨constant, nonnegative, bound⟩ :=
    (actualDifferentiatedPhysicalBoundaryKernel_uniformMoments parameters L compact).oneHigh_bound
      (fun state => state.val.size_nonnegative) grade
  refine ⟨constant, nonnegative, ?_⟩
  intro rho alpha delta parameter epsilon field small compactNonnegative alphaSmall deltaSmall parameterSmall high low compatible
  have estimate := bound (PhysicalBoundaryState.of parameters L compact rho alpha delta parameter epsilon field
    small compactNonnegative alphaSmall deltaSmall parameterSmall) high low
  change ‖fullOneHighKernelAction parameters grade
    (actualDifferentiatedPhysicalBoundaryKernel parameters L rho alpha delta parameter epsilon compact field
      small compactNonnegative alphaSmall deltaSmall parameterSmall) high low‖ ≤ _
  simpa only [BoundaryReconstructionState.size, PhysicalBoundaryState.of,
    BoundaryReconstructionState.of, BoundaryReconstructionState.rho,
    BoundaryReconstructionState.alpha, BoundaryReconstructionState.delta,
    BoundaryReconstructionState.parameter, BoundaryReconstructionState.epsilon,
    BoundaryReconstructionState.field, BoundaryReconstructionData.rho,
    BoundaryReconstructionData.alpha, BoundaryReconstructionData.delta,
    BoundaryReconstructionData.parameter, BoundaryReconstructionData.epsilon,
    BoundaryReconstructionData.field, Nat.add_assoc, Nat.reduceAdd] using estimate

end Grad.ActualBoundaryPrimitives
