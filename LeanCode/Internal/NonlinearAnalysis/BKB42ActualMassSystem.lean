import BKB41ActualReconstructionKernels

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Allocation

def actualSigmaComponentBoundaryKernel (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) (component : Fin 3) :
    FullTwoFrequencyKernel parameters 1 1 :=
  boundaryScalarMultiplicationKernel parameters 1
    (actualSigmaBoundaryCoefficients parameters L rho epsilon field low component)
    (actualSigmaBoundaryCoefficients_moments parameters L rho epsilon field low
      component)

def actualRotatedSigmaComponentBoundaryKernel (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) (component : Fin 3) :
    FullTwoFrequencyKernel parameters 1 1 :=
  boundaryScalarMultiplicationKernel parameters 1
    (actualRotatedSigmaBoundaryCoefficients parameters L rho epsilon field low
      component)
    (actualRotatedSigmaBoundaryCoefficients_moments parameters L rho epsilon field
      low component)

/-- AF12's exact known term
`j_*=(R delta-sigma)a_*+delta-sigma Ra_*+(R kappa1)xi+kappa1 Rxi`. -/
def actualKnownJStarKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 7 1 :=
  let smallGauge := small.trans
    (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius)
  let smallSix := (physicalBudget_monotone parameters field rho epsilon
    (by omega : 6 ≤ 7)).trans smallGauge
  let coefficientLow := smallSix.trans
    (actualGaugeInverseLowRadius_le_original parameters L compactRadius)
  fullKernelComposition (angularMeanFreeKernel parameters 1)
    (fullKernelAdd
      (fullKernelAdd
        (fullKernelComposition
          (actualRotatedSigmaBoundaryKernel parameters L rho epsilon field
            coefficientLow)
          (actualKnownAStarKernel parameters L rho alpha delta parameter epsilon
            compactRadius field small compactNonnegative alphaSmall deltaSmall
            parameterSmall))
        (fullKernelComposition
          (actualSigmaBoundaryKernel parameters L rho epsilon field coefficientLow)
          (actualKnownRAStarKernel parameters L rho alpha delta parameter epsilon
            compactRadius field small compactNonnegative alphaSmall deltaSmall
            parameterSmall)))
      (fullKernelAdd
        (fullKernelComposition
          (actualRotatedSigmaComponentBoundaryKernel parameters L rho epsilon field
            coefficientLow 1)
          (sevenInputSlotKernel parameters 3))
        (fullKernelComposition
          (actualSigmaComponentBoundaryKernel parameters L rho epsilon field
            coefficientLow 1)
          (sevenInputSlotKernel parameters 1))))

/-- AF12's exact zero-order perturbation `T_b A`. -/
def actualMassPerturbationKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 1 1 :=
  let smallGauge := small.trans
    (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius)
  let smallSix := (physicalBudget_monotone parameters field rho epsilon
    (by omega : 6 ≤ 7)).trans smallGauge
  let coefficientLow := smallSix.trans
    (actualGaugeInverseLowRadius_le_original parameters L compactRadius)
  fullKernelComposition (angularMeanFreeKernel parameters 1)
    (fullKernelAdd
      (fullKernelComposition
        (actualRotatedSigmaBoundaryKernel parameters L rho epsilon field coefficientLow)
        (actualUnknownUKernel parameters L rho alpha delta parameter epsilon
          compactRadius field small compactNonnegative alphaSmall deltaSmall
          parameterSmall))
      (fullKernelComposition
        (actualSigmaBoundaryKernel parameters L rho epsilon field coefficientLow)
        (actualUnknownVKernel parameters L rho alpha delta parameter epsilon
          compactRadius field small compactNonnegative alphaSmall deltaSmall
          parameterSmall)))

end Grad.BoundaryKernelAction
