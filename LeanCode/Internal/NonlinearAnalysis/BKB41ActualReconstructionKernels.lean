import BKB40ActualEncodedFirstInverse

noncomputable section

set_option maxHeartbeats 1400000

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation

def actualKnownEncodedWKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 7 3 :=
  let smallGauge := small.trans
    (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius)
  let smallSix := (physicalBudget_monotone parameters field rho epsilon
    (by omega : 6 ≤ 7)).trans smallGauge
  fullKernelComposition
    (actualEncodedFirstInverseKernel parameters L rho alpha delta parameter epsilon
      compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
    (actualKnownEncodedDataKernel parameters L rho alpha delta parameter epsilon
      compactRadius field smallSix compactNonnegative alphaSmall deltaSmall parameterSmall)

/-- AF4's actual known reconstruction `a_*`. -/
def actualKnownAStarKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 7 3 :=
  let smallGauge := small.trans
    (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius)
  let smallSix := (physicalBudget_monotone parameters field rho epsilon
    (by omega : 6 ≤ 7)).trans smallGauge
  fullKernelComposition
    (actualGaugeQKernelOnBall parameters L rho alpha delta parameter epsilon
      compactRadius field smallSix compactNonnegative alphaSmall deltaSmall
      parameterSmall)
    (fullKernelAdd
      (fullKernelComposition (encodedJKernel parameters)
        (actualKnownEncodedWKernel parameters L rho alpha delta parameter epsilon
          compactRadius field small compactNonnegative alphaSmall deltaSmall
          parameterSmall))
      (fullKernelComposition (secondCoordinateInjectionKernel parameters)
        (sevenInputSlotKernel parameters 3)))

/-- AF7's exact `Ra_*=(0,KY_*+Rxi,C_*)`. -/
def actualKnownRAStarKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 7 3 :=
  fullKernelAdd
    (fullKernelComposition (encodedRotationKernel parameters)
      (actualKnownEncodedWKernel parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall
        parameterSmall))
    (actualKnownRotatedQStarKernel parameters)

def actualUnknownQAKernel (parameters : PhaseParameters) :
    FullTwoFrequencyKernel parameters 1 3 :=
  fullKernelComposition (firstCoordinateInjectionKernel parameters)
    (angularInverseKernel parameters 1)

def actualUnknownN0Kernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 1 3 :=
  let smallGauge := small.trans
    (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius)
  let smallSix := (physicalBudget_monotone parameters field rho epsilon
    (by omega : 6 ≤ 7)).trans smallGauge
  fullKernelComposition (firstCoordinateInjectionKernel parameters)
    (fullKernelNeg
      (fullKernelComposition (angularMeanKernel parameters 1)
        (fullKernelComposition
          (actualForceBoundaryKernel parameters L rho epsilon field 0
            (smallSix.trans (actualGaugeInverseLowRadius_le_original parameters L
              compactRadius)))
          (fullKernelComposition
            (actualGaugeQKernelOnBall parameters L rho alpha delta parameter epsilon
              compactRadius field smallSix compactNonnegative alphaSmall deltaSmall
              parameterSmall)
            (actualUnknownQAKernel parameters)))))

def actualUnknownN1Kernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 1 3 :=
  let smallGauge := small.trans
    (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius)
  let smallSix := (physicalBudget_monotone parameters field rho epsilon
    (by omega : 6 ≤ 7)).trans smallGauge
  let qA := fullKernelComposition
    (actualGaugeQKernelOnBall parameters L rho alpha delta parameter epsilon
      compactRadius field smallSix compactNonnegative alphaSmall deltaSmall
      parameterSmall)
    (actualUnknownQAKernel parameters)
  fullKernelComposition (secondCoordinateInjectionKernel parameters)
    (fullKernelSub
      (fullKernelSmul 2 (fullIdentityKernel parameters 1))
      (fullKernelAdd
        (fullKernelComposition
          (actualRotatedForceBoundaryKernel parameters L rho epsilon field 0
            (smallSix.trans (actualGaugeInverseLowRadius_le_original parameters L
              compactRadius))) qA)
        (fullKernelComposition
          (actualForceBoundaryKernel parameters L rho epsilon field 0
            (smallSix.trans (actualGaugeInverseLowRadius_le_original parameters L
              compactRadius)))
          (firstCoordinateInjectionKernel parameters))))

def actualUnknownN2Kernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 1 3 :=
  let smallGauge := small.trans
    (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius)
  let smallSix := (physicalBudget_monotone parameters field rho epsilon
    (by omega : 6 ≤ 7)).trans smallGauge
  let qA := fullKernelComposition
    (actualGaugeQKernelOnBall parameters L rho alpha delta parameter epsilon
      compactRadius field smallSix compactNonnegative alphaSmall deltaSmall
      parameterSmall)
    (actualUnknownQAKernel parameters)
  fullKernelComposition (thirdCoordinateInjectionKernel parameters)
    (fullKernelNeg
      (fullKernelComposition (angularMeanFreeKernel parameters 1)
        (fullKernelComposition
          (actualForceBoundaryKernel parameters L rho epsilon field 1
            (smallSix.trans (actualGaugeInverseLowRadius_le_original parameters L
              compactRadius))) qA)))

def actualUnknownNKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 1 3 :=
  fullKernelAdd
    (actualUnknownN0Kernel parameters L rho alpha delta parameter epsilon
      compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
    (fullKernelAdd
      (actualUnknownN1Kernel parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
      (actualUnknownN2Kernel parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall))

def actualUnknownWKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 1 3 :=
  fullKernelComposition
    (actualEncodedFirstInverseKernel parameters L rho alpha delta parameter epsilon
      compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
    (actualUnknownNKernel parameters L rho alpha delta parameter epsilon compactRadius
      field small compactNonnegative alphaSmall deltaSmall parameterSmall)

/-- AF5's actual `U_b`. -/
def actualUnknownUKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 1 3 :=
  let smallGauge := small.trans
    (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius)
  let smallSix := (physicalBudget_monotone parameters field rho epsilon
    (by omega : 6 ≤ 7)).trans smallGauge
  fullKernelComposition
    (actualGaugeQKernelOnBall parameters L rho alpha delta parameter epsilon
      compactRadius field smallSix compactNonnegative alphaSmall deltaSmall
      parameterSmall)
    (fullKernelAdd
      (fullKernelComposition (encodedJKernel parameters)
        (actualUnknownWKernel parameters L rho alpha delta parameter epsilon
          compactRadius field small compactNonnegative alphaSmall deltaSmall
          parameterSmall))
      (actualUnknownQAKernel parameters))

/-- AF6's actual `V_b`. -/
def actualUnknownVKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 1 3 :=
  fullKernelAdd
    (fullKernelComposition (encodedRotationKernel parameters)
      (actualUnknownWKernel parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall
        parameterSmall))
    (firstCoordinateInjectionKernel parameters)

end Grad.BoundaryKernelAction
