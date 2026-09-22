import BKB50EncodedD0Inverse

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.CartesianState

theorem fullKernelPositiveIdentityInverse_right {dimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 (fullKernelNeg kernel) ≤ low)
    (lowSmall : low < 1) :
    fullKernelComposition
        (fullKernelAdd (fullIdentityKernel parameters dimension) kernel)
        (fullKernelNeg (fullKernelNegativeIdentityInverse parameters
          (fullKernelNeg kernel) low lowBound lowSmall)) =
      fullIdentityKernel parameters dimension := by
  have inverse := fullKernelNegativeIdentity_inverse_right parameters
    (fullKernelNeg kernel) low lowBound lowSmall
  calc
    fullKernelComposition
        (fullKernelAdd (fullIdentityKernel parameters dimension) kernel)
        (fullKernelNeg (fullKernelNegativeIdentityInverse parameters
          (fullKernelNeg kernel) low lowBound lowSmall)) =
      fullKernelComposition
        (fullKernelNegativeIdentityPerturbation parameters (fullKernelNeg kernel))
        (fullKernelNegativeIdentityInverse parameters
          (fullKernelNeg kernel) low lowBound lowSmall) := by
        rw [fullKernelComposition_neg_inner, fullKernelComposition_add_outer]
        unfold fullKernelNegativeIdentityPerturbation fullKernelSub
        rw [fullKernelComposition_add_outer]
        simp_rw [fullKernelComposition_neg_outer]
        apply FullTwoFrequencyKernel.ext_entry
        intro shift input
        simp only [fullKernelNeg_entry, fullKernelAdd_entry]
        abel
    _ = fullIdentityKernel parameters dimension := inverse

theorem fullKernelPositiveIdentityInverse_left {dimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 (fullKernelNeg kernel) ≤ low)
    (lowSmall : low < 1) :
    fullKernelComposition
        (fullKernelNeg (fullKernelNegativeIdentityInverse parameters
          (fullKernelNeg kernel) low lowBound lowSmall))
        (fullKernelAdd (fullIdentityKernel parameters dimension) kernel) =
      fullIdentityKernel parameters dimension := by
  have inverse := fullKernelNegativeIdentity_inverse_left parameters
    (fullKernelNeg kernel) low lowBound lowSmall
  calc
    fullKernelComposition
        (fullKernelNeg (fullKernelNegativeIdentityInverse parameters
          (fullKernelNeg kernel) low lowBound lowSmall))
        (fullKernelAdd (fullIdentityKernel parameters dimension) kernel) =
      fullKernelComposition
        (fullKernelNegativeIdentityInverse parameters
          (fullKernelNeg kernel) low lowBound lowSmall)
        (fullKernelNegativeIdentityPerturbation parameters (fullKernelNeg kernel)) := by
        rw [fullKernelComposition_neg_outer, fullKernelComposition_add_inner]
        unfold fullKernelNegativeIdentityPerturbation fullKernelSub
        rw [fullKernelComposition_add_inner]
        simp_rw [fullKernelComposition_neg_inner]
        apply FullTwoFrequencyKernel.ext_entry
        intro shift input
        simp only [fullKernelNeg_entry, fullKernelAdd_entry]
        abel
    _ = fullIdentityKernel parameters dimension := inverse

end Grad.BoundaryKernelAction
