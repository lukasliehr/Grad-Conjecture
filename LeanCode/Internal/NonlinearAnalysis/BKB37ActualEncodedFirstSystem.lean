import BKB36ActualGaugeLowBall

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation

/-- `Q_b J` on the complete encoded three-component trace. -/
def actualGaugeDecodedKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 3 3 :=
  fullKernelComposition
    (actualGaugeQKernelOnBall parameters L rho alpha delta parameter epsilon
      compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
    (encodedJKernel parameters)

/-- The known `Q_b q_*`, where `q_*=(0,xi,0)` is AH20 slot three. -/
def actualKnownQStarKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 7 3 :=
  fullKernelComposition
    (actualGaugeQKernelOnBall parameters L rho alpha delta parameter epsilon
      compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
    (fullKernelComposition (secondCoordinateInjectionKernel parameters)
      (sevenInputSlotKernel parameters 3))

/-- AE16 gives `R(Q_b q_*)=(0,Rxi,0)`; no derivative of the angularly
constant gauge correction is inserted. -/
def actualKnownRotatedQStarKernel (parameters : PhaseParameters) :
    FullTwoFrequencyKernel parameters 7 3 :=
  fullKernelComposition (secondCoordinateInjectionKernel parameters)
    (sevenInputSlotKernel parameters 1)

def actualKnownEncodedD0Kernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 7 3 :=
  fullKernelComposition (firstCoordinateInjectionKernel parameters)
    (fullKernelSub
      (fullKernelComposition (angularMeanKernel parameters 1)
        (sevenInputSlotKernel parameters 4))
      (fullKernelComposition (angularMeanKernel parameters 1)
        (fullKernelComposition
          (actualForceBoundaryKernel parameters L rho epsilon field 0
            (small.trans (actualGaugeInverseLowRadius_le_original parameters L
              compactRadius)))
          (actualKnownQStarKernel parameters L rho alpha delta parameter epsilon
            compactRadius field small compactNonnegative alphaSmall deltaSmall
            parameterSmall))))

def actualKnownEncodedD1Kernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 7 3 :=
  fullKernelComposition (secondCoordinateInjectionKernel parameters)
    (fullKernelSub (sevenInputSlotKernel parameters 5)
      (fullKernelComposition (angularMeanFreeKernel parameters 1)
        (fullKernelAdd
          (fullKernelComposition
            (actualRotatedForceBoundaryKernel parameters L rho epsilon field 0
              (small.trans (actualGaugeInverseLowRadius_le_original parameters L
                compactRadius)))
            (actualKnownQStarKernel parameters L rho alpha delta parameter epsilon
              compactRadius field small compactNonnegative alphaSmall deltaSmall
              parameterSmall))
          (fullKernelComposition
            (actualForceBoundaryKernel parameters L rho epsilon field 0
              (small.trans (actualGaugeInverseLowRadius_le_original parameters L
                compactRadius)))
            (actualKnownRotatedQStarKernel parameters)))))

def actualKnownEncodedD2Kernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 7 3 :=
  fullKernelComposition (thirdCoordinateInjectionKernel parameters)
    (fullKernelSub
      (fullKernelAdd (sevenInputSlotKernel parameters 6)
        (fullKernelSmul (L : ℂ)⁻¹ (sevenInputSlotKernel parameters 2)))
      (fullKernelComposition (angularMeanFreeKernel parameters 1)
        (fullKernelComposition
          (actualForceBoundaryKernel parameters L rho epsilon field 1
            (small.trans (actualGaugeInverseLowRadius_le_original parameters L
              compactRadius)))
          (actualKnownQStarKernel parameters L rho alpha delta parameter epsilon
            compactRadius field small compactNonnegative alphaSmall deltaSmall
            parameterSmall))))

/-- AE17's exact known encoded right-hand side on the seven AH20 slots. -/
def actualKnownEncodedDataKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 7 3 :=
  fullKernelAdd
    (actualKnownEncodedD0Kernel parameters L rho alpha delta parameter epsilon
      compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
    (fullKernelAdd
      (actualKnownEncodedD1Kernel parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
      (actualKnownEncodedD2Kernel parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall))

def actualEncodedE0Kernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 3 3 :=
  fullKernelComposition (firstCoordinateInjectionKernel parameters)
    (fullKernelComposition (angularMeanKernel parameters 1)
      (fullKernelComposition
        (actualForceBoundaryKernel parameters L rho epsilon field 0
          (small.trans (actualGaugeInverseLowRadius_le_original parameters L
            compactRadius)))
        (actualGaugeDecodedKernel parameters L rho alpha delta parameter epsilon
          compactRadius field small compactNonnegative alphaSmall deltaSmall
          parameterSmall)))

def actualEncodedE1Kernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 3 3 :=
  fullKernelComposition (secondCoordinateInjectionKernel parameters)
    (fullKernelComposition (angularMeanFreeKernel parameters 1)
      (fullKernelAdd
        (fullKernelComposition
          (actualRotatedForceBoundaryKernel parameters L rho epsilon field 0
            (small.trans (actualGaugeInverseLowRadius_le_original parameters L
              compactRadius)))
          (actualGaugeDecodedKernel parameters L rho alpha delta parameter epsilon
            compactRadius field small compactNonnegative alphaSmall deltaSmall
            parameterSmall))
        (fullKernelComposition
          (actualForceBoundaryKernel parameters L rho epsilon field 0
            (small.trans (actualGaugeInverseLowRadius_le_original parameters L
              compactRadius)))
          (encodedRotationKernel parameters))))

def actualEncodedE2Kernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 3 3 :=
  fullKernelComposition (thirdCoordinateInjectionKernel parameters)
    (fullKernelComposition (angularMeanFreeKernel parameters 1)
      (fullKernelComposition
        (actualForceBoundaryKernel parameters L rho epsilon field 1
          (small.trans (actualGaugeInverseLowRadius_le_original parameters L
            compactRadius)))
        (actualGaugeDecodedKernel parameters L rho alpha delta parameter epsilon
          compactRadius field small compactNonnegative alphaSmall deltaSmall
          parameterSmall)))

/-- AE18's exact input-mode-dependent perturbation. -/
def actualEncodedPerturbationKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 3 3 :=
  fullKernelAdd
    (actualEncodedE0Kernel parameters L rho alpha delta parameter epsilon
      compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
    (fullKernelAdd
      (actualEncodedE1Kernel parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
      (actualEncodedE2Kernel parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall))

def actualPreconditionedEncodedPerturbationKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 3 3 :=
  fullKernelComposition (encodedD0InverseKernel parameters)
    (actualEncodedPerturbationKernel parameters L rho alpha delta parameter
      epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
      parameterSmall)

end Grad.BoundaryKernelAction
