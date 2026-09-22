import BKB45ActualMassInverse

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Physical.Allocation

/-- The ambient full-kernel formula for AF16's inhomogeneous right-hand side
`Rp-j_*`, on AH20's seven slots.  The AE14 support invariants needed to
interpret this as the physical restricted system are proved separately. -/
def actualMassRightHandKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 7 1 :=
  fullKernelSub (sevenInputSlotKernel parameters 0)
    (actualKnownJStarKernel parameters L rho alpha delta parameter epsilon
      compactRadius field
        (small.trans (actualMassInverseLowRadius_le_first parameters L compactRadius))
      compactNonnegative alphaSmall deltaSmall parameterSmall)

/-- The ambient full-kernel recovered mass formula `A=H_b(Rp-j_*)`.
Mean-free preservation on the encoded AE14 support is a separate obligation. -/
def actualRecoveredMassKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 7 1 :=
  fullKernelComposition
    (actualMassInverseKernel parameters L rho alpha delta parameter epsilon
      compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
    (actualMassRightHandKernel parameters L rho alpha delta parameter epsilon
      compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)

/-- The ambient full-kernel covariant formula `a_c=U_b A+a_*`. -/
def actualCovariantKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 7 3 :=
  let smallFirst := small.trans
    (actualMassInverseLowRadius_le_first parameters L compactRadius)
  fullKernelAdd
    (fullKernelComposition
      (actualUnknownUKernel parameters L rho alpha delta parameter epsilon
        compactRadius field smallFirst compactNonnegative alphaSmall deltaSmall parameterSmall)
      (actualRecoveredMassKernel parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall))
    (actualKnownAStarKernel parameters L rho alpha delta parameter epsilon
      compactRadius field smallFirst compactNonnegative alphaSmall deltaSmall parameterSmall)

/-- The ambient full-kernel formula denoted `Ra_c=V_b A+Ra_*`.  This name
records the algebraic angular row; equality with the genuine physical
rotation of `a_c` requires the remaining AE14 mean-zero/rotation bridge. -/
def actualRotatedCovariantKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 7 3 :=
  let smallFirst := small.trans
    (actualMassInverseLowRadius_le_first parameters L compactRadius)
  fullKernelAdd
    (fullKernelComposition
      (actualUnknownVKernel parameters L rho alpha delta parameter epsilon
        compactRadius field smallFirst compactNonnegative alphaSmall deltaSmall parameterSmall)
      (actualRecoveredMassKernel parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall))
    (actualKnownRAStarKernel parameters L rho alpha delta parameter epsilon
      compactRadius field smallFirst compactNonnegative alphaSmall deltaSmall parameterSmall)

end Grad.BoundaryKernelAction
