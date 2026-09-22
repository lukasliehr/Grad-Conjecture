import BKB21NeumannTailAlgebra

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.BoundaryKernelAction

open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace

theorem fullKernelSub_comp
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (first second : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension) :
    fullKernelComposition (fullKernelSub first second) inner =
      fullKernelSub (fullKernelComposition first inner)
        (fullKernelComposition second inner) := by
  unfold fullKernelSub
  rw [fullKernelComposition_add_outer, fullKernelComposition_neg_outer]

theorem fullKernel_comp_sub
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (first second : FullTwoFrequencyKernel parameters inputDimension middleDimension) :
    fullKernelComposition outer (fullKernelSub first second) =
      fullKernelSub (fullKernelComposition outer first)
        (fullKernelComposition outer second) := by
  unfold fullKernelSub
  rw [fullKernelComposition_add_inner, fullKernelComposition_neg_inner]

/-- `I + K + K² + ...` for the exact input-dependent full kernel. -/
def fullKernelNeumannSum {dimension : ℕ} (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) :
    FullTwoFrequencyKernel parameters dimension dimension :=
  fullKernelAdd (fullIdentityKernel parameters dimension)
    (fullKernelNeumannTail parameters kernel low lowBound lowSmall)

theorem fullKernel_comp_neumannSum {dimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) :
    fullKernelComposition kernel
        (fullKernelNeumannSum parameters kernel low lowBound lowSmall) =
      fullKernelNeumannTail parameters kernel low lowBound lowSmall := by
  unfold fullKernelNeumannSum
  rw [fullKernelComposition_add_inner, fullKernel_comp_identity,
    fullKernel_comp_neumannTail]
  apply FullTwoFrequencyKernel.ext_entry
  intro shift input
  rw [fullKernelAdd_entry, fullKernelSub_entry]
  abel

theorem fullKernelNeumannSum_comp {dimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) :
    fullKernelComposition
        (fullKernelNeumannSum parameters kernel low lowBound lowSmall) kernel =
      fullKernelNeumannTail parameters kernel low lowBound lowSmall := by
  unfold fullKernelNeumannSum
  rw [fullKernelComposition_add_outer, fullIdentityKernel_comp,
    fullKernelNeumannTail_comp]
  apply FullTwoFrequencyKernel.ext_entry
  intro shift input
  rw [fullKernelAdd_entry, fullKernelSub_entry]
  abel

/-- The literal AF matrix is `-I + T = T - I`. -/
def fullKernelNegativeIdentityPerturbation {dimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension) :
    FullTwoFrequencyKernel parameters dimension dimension :=
  fullKernelSub kernel (fullIdentityKernel parameters dimension)

/-- The exact inverse of `-I + T` is `-(I + T + T² + ...)`. -/
def fullKernelNegativeIdentityInverse {dimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) :
    FullTwoFrequencyKernel parameters dimension dimension :=
  fullKernelNeg (fullKernelNeumannSum parameters kernel low lowBound lowSmall)

theorem fullKernelNegativeIdentity_inverse_right {dimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) :
    fullKernelComposition
        (fullKernelNegativeIdentityPerturbation parameters kernel)
        (fullKernelNegativeIdentityInverse parameters kernel low lowBound lowSmall) =
      fullIdentityKernel parameters dimension := by
  unfold fullKernelNegativeIdentityPerturbation
    fullKernelNegativeIdentityInverse
  rw [fullKernelComposition_neg_inner, fullKernelSub_comp,
    fullKernel_comp_neumannSum, fullIdentityKernel_comp]
  apply FullTwoFrequencyKernel.ext_entry
  intro shift input
  unfold fullKernelNeumannSum
  rw [fullKernelNeg_entry, fullKernelSub_entry, fullKernelAdd_entry]
  abel

theorem fullKernelNegativeIdentity_inverse_left {dimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) :
    fullKernelComposition
        (fullKernelNegativeIdentityInverse parameters kernel low lowBound lowSmall)
        (fullKernelNegativeIdentityPerturbation parameters kernel) =
      fullIdentityKernel parameters dimension := by
  unfold fullKernelNegativeIdentityPerturbation
    fullKernelNegativeIdentityInverse
  rw [fullKernelComposition_neg_outer, fullKernel_comp_sub,
    fullKernelNeumannSum_comp, fullKernel_comp_identity]
  apply FullTwoFrequencyKernel.ext_entry
  intro shift input
  unfold fullKernelNeumannSum
  rw [fullKernelNeg_entry, fullKernelSub_entry, fullKernelAdd_entry]
  abel

end Grad.BoundaryKernelAction
