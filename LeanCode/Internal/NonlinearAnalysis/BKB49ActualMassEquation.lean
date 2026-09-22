import BKB48ActualCovariantAction

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Physical.Allocation

theorem fullIdentityKernel_comp_rect
    {inputDimension outputDimension : ℕ} (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters inputDimension outputDimension) :
    fullKernelComposition (fullIdentityKernel parameters outputDimension) kernel = kernel := by
  apply FullTwoFrequencyKernel.ext_entry
  intro total input
  rw [fullKernelComposition_entry,
    tsum_eq_single total (by
      intro middle distinct
      have nonzero : total - middle ≠ (0, 0) := by
        intro zero
        apply distinct
        have firstCoordinate := congrArg Prod.fst zero
        have secondCoordinate := congrArg Prod.snd zero
        apply Prod.ext <;> dsimp at firstCoordinate secondCoordinate ⊢ <;> omega
      rw [fullIdentityKernel_entry_ne_zero parameters outputDimension
        (total - middle) (input + middle) nonzero]
      simp)]
  rw [show total - total = (0, 0) by exact sub_self total]
  rw [fullIdentityKernel_entry_zero]
  simp

theorem actualMassInverseKernel_right (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    let smallFirst := small.trans
      (actualMassInverseLowRadius_le_first parameters L compactRadius)
    let mass := actualMassPerturbationKernel parameters L rho alpha delta parameter
      epsilon compactRadius field smallFirst compactNonnegative alphaSmall deltaSmall
      parameterSmall
    fullKernelComposition
        (fullKernelNegativeIdentityPerturbation parameters mass)
        (actualMassInverseKernel parameters L rho alpha delta parameter epsilon
          compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) =
      fullIdentityKernel parameters 1 := by
  dsimp only
  unfold actualMassInverseKernel
  exact fullKernelNegativeIdentity_inverse_right parameters _ (1 / 2)
    (actualMassPerturbationKernel_moment_zero_le_half parameters L rho alpha delta
      parameter epsilon compactRadius field small compactNonnegative alphaSmall
      deltaSmall parameterSmall) (by norm_num)

/-- AF16 solves the actual inhomogeneous encoded mass equation exactly. -/
theorem actualRecoveredMassKernel_solves (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    let smallFirst := small.trans
      (actualMassInverseLowRadius_le_first parameters L compactRadius)
    let mass := actualMassPerturbationKernel parameters L rho alpha delta parameter
      epsilon compactRadius field smallFirst compactNonnegative alphaSmall deltaSmall
      parameterSmall
    fullKernelComposition
        (fullKernelNegativeIdentityPerturbation parameters mass)
        (actualRecoveredMassKernel parameters L rho alpha delta parameter epsilon
          compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall) =
      actualMassRightHandKernel parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall := by
  dsimp only
  unfold actualRecoveredMassKernel
  rw [← fullKernelComposition_assoc,
    actualMassInverseKernel_right parameters L rho alpha delta parameter epsilon
      compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall,
    fullIdentityKernel_comp_rect]

end Grad.BoundaryKernelAction
