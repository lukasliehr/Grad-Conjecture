import BKB43FirstInverseMoments

noncomputable section

set_option maxHeartbeats 2000000

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation

def actualUnknownNBaseConstant (parameters : PhaseParameters)
    (L compactRadius : ℝ) : ℝ :=
  let q := actualGaugeUnknownQABaseConstant parameters L compactRadius
  let first := fullKernelMoment parameters 0 (firstCoordinateInjectionKernel parameters) *
    (fullKernelMoment parameters 0 (angularMeanKernel parameters 1) *
      (actualForce0BaseConstant parameters L * q))
  let second := fullKernelMoment parameters 0 (secondCoordinateInjectionKernel parameters) *
    (fullKernelMoment parameters 0
        (fullKernelSmul 2 (fullIdentityKernel parameters 1)) +
      actualRotatedForce0BaseConstant parameters L * q +
      actualForce0BaseConstant parameters L *
        fullKernelMoment parameters 0 (firstCoordinateInjectionKernel parameters))
  let third := fullKernelMoment parameters 0 (thirdCoordinateInjectionKernel parameters) *
    (fullKernelMoment parameters 0 (angularMeanFreeKernel parameters 1) *
      (actualForce2BaseConstant parameters L * q))
  first + second + third

theorem actualUnknownNBaseConstant_nonnegative (parameters : PhaseParameters)
    (L compactRadius : ℝ) :
    0 ≤ actualUnknownNBaseConstant parameters L compactRadius := by
  unfold actualUnknownNBaseConstant actualGaugeUnknownQABaseConstant
    actualUnknownQABaseConstant
  dsimp only
  have q : 0 ≤ actualGaugeQBaseConstant parameters L compactRadius *
      fullKernelMoment parameters 0 (actualUnknownQAKernel parameters) :=
    mul_nonneg (actualGaugeQBaseConstant_nonnegative parameters L compactRadius)
      (fullKernelMoment_nonnegative parameters 0 _)
  have f0 := actualForce0BaseConstant_nonnegative parameters L
  have rf0 := actualRotatedForce0BaseConstant_nonnegative parameters L
  have f2 := actualForce2BaseConstant_nonnegative parameters L
  apply add_nonneg
  · apply add_nonneg
    · exact mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
        (mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
          (mul_nonneg f0 q))
    · exact mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
        (add_nonneg
          (add_nonneg (fullKernelMoment_nonnegative parameters 0 _)
            (mul_nonneg rf0 q))
          (mul_nonneg f0 (fullKernelMoment_nonnegative parameters 0 _)))
  · exact mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
      (mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
        (mul_nonneg f2 q))

def actualUnknownWBaseConstant (parameters : PhaseParameters)
    (L compactRadius : ℝ) : ℝ :=
  actualEncodedFirstInverseBaseConstant parameters *
    actualUnknownNBaseConstant parameters L compactRadius

def actualUnknownUBaseConstant (parameters : PhaseParameters)
    (L compactRadius : ℝ) : ℝ :=
  actualGaugeQBaseConstant parameters L compactRadius *
    (fullKernelMoment parameters 0 (encodedJKernel parameters) *
      actualUnknownWBaseConstant parameters L compactRadius +
      actualUnknownQABaseConstant parameters)

def actualUnknownVBaseConstant (parameters : PhaseParameters)
    (L compactRadius : ℝ) : ℝ :=
  fullKernelMoment parameters 0 (encodedRotationKernel parameters) *
    actualUnknownWBaseConstant parameters L compactRadius +
  fullKernelMoment parameters 0 (firstCoordinateInjectionKernel parameters)

theorem actualUnknownUBaseConstant_nonnegative (parameters : PhaseParameters)
    (L compactRadius : ℝ) :
    0 ≤ actualUnknownUBaseConstant parameters L compactRadius := by
  unfold actualUnknownUBaseConstant actualUnknownWBaseConstant
    actualUnknownQABaseConstant
  exact mul_nonneg (actualGaugeQBaseConstant_nonnegative parameters L compactRadius)
    (add_nonneg
      (mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
        (mul_nonneg (actualEncodedFirstInverseBaseConstant_nonnegative parameters)
          (actualUnknownNBaseConstant_nonnegative parameters L compactRadius)))
      (fullKernelMoment_nonnegative parameters 0 _))

theorem actualUnknownVBaseConstant_nonnegative (parameters : PhaseParameters)
    (L compactRadius : ℝ) :
    0 ≤ actualUnknownVBaseConstant parameters L compactRadius := by
  unfold actualUnknownVBaseConstant actualUnknownWBaseConstant
  exact add_nonneg
    (mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
      (mul_nonneg (actualEncodedFirstInverseBaseConstant_nonnegative parameters)
        (actualUnknownNBaseConstant_nonnegative parameters L compactRadius)))
    (fullKernelMoment_nonnegative parameters 0 _)

theorem actualUnknownUVKernel_moment_zero_le (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    fullKernelMoment parameters 0
        (actualUnknownUKernel parameters L rho alpha delta parameter epsilon
          compactRadius field small compactNonnegative alphaSmall deltaSmall
          parameterSmall) ≤ actualUnknownUBaseConstant parameters L compactRadius ∧
      fullKernelMoment parameters 0
        (actualUnknownVKernel parameters L rho alpha delta parameter epsilon
          compactRadius field small compactNonnegative alphaSmall deltaSmall
          parameterSmall) ≤ actualUnknownVBaseConstant parameters L compactRadius := by
  let smallGauge := small.trans
    (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius)
  let smallSix := (physicalBudget_monotone parameters field rho epsilon
    (by omega : 6 ≤ 7)).trans smallGauge
  let coefficientLow := smallSix.trans
    (actualGaugeInverseLowRadius_le_original parameters L compactRadius)
  let qA := fullKernelComposition
    (actualGaugeQKernelOnBall parameters L rho alpha delta parameter epsilon
      compactRadius field smallSix compactNonnegative alphaSmall deltaSmall
      parameterSmall) (actualUnknownQAKernel parameters)
  have budgetOne : physicalBudget parameters field rho epsilon 7 ≤ 1 :=
    small.trans ((actualEncodedFirstLowRadius_le_gauge parameters L compactRadius).trans
      ((actualGaugeInverseLowRadius_le_original parameters L compactRadius).trans
        (min_le_left _ _)))
  have qABound := actualGaugeUnknownQAKernel_moment_zero_le parameters L rho alpha
    delta parameter epsilon compactRadius field small compactNonnegative alphaSmall
    deltaSmall parameterSmall
  have force0raw := actualForceBoundaryKernel_moment_le parameters L rho epsilon field
    0 coefficientLow 0
  have force0 : fullKernelMoment parameters 0
      (actualForceBoundaryKernel parameters L rho epsilon field 0 coefficientLow) ≤
      actualForce0BaseConstant parameters L := by
    change _ ≤ actualForce0BaseConstant parameters L *
      physicalBudget parameters field rho epsilon 6 at force0raw
    exact force0raw.trans ((mul_le_mul_of_nonneg_left
      ((physicalBudget_monotone parameters field rho epsilon (by omega : 6 ≤ 7)).trans
        budgetOne) (actualForce0BaseConstant_nonnegative parameters L)).trans_eq
      (mul_one _))
  have rotatedRaw := actualRotatedForceBoundaryKernel_moment_le parameters L rho
    epsilon field 0 coefficientLow 0
  have rotatedForce0 : fullKernelMoment parameters 0
      (actualRotatedForceBoundaryKernel parameters L rho epsilon field 0 coefficientLow) ≤
      actualRotatedForce0BaseConstant parameters L := by
    change _ ≤ actualRotatedForce0BaseConstant parameters L *
      physicalBudget parameters field rho epsilon 7 at rotatedRaw
    exact rotatedRaw.trans ((mul_le_mul_of_nonneg_left budgetOne
      (actualRotatedForce0BaseConstant_nonnegative parameters L)).trans_eq (mul_one _))
  have force2raw := actualForceBoundaryKernel_moment_le parameters L rho epsilon field
    1 coefficientLow 0
  have force2 : fullKernelMoment parameters 0
      (actualForceBoundaryKernel parameters L rho epsilon field 1 coefficientLow) ≤
      actualForce2BaseConstant parameters L := by
    change _ ≤ actualForce2BaseConstant parameters L *
      physicalBudget parameters field rho epsilon 6 at force2raw
    exact force2raw.trans ((mul_le_mul_of_nonneg_left
      ((physicalBudget_monotone parameters field rho epsilon (by omega : 6 ≤ 7)).trans
        budgetOne) (actualForce2BaseConstant_nonnegative parameters L)).trans_eq
      (mul_one _))
  have n0 : fullKernelMoment parameters 0
      (actualUnknownN0Kernel parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall
        parameterSmall) ≤
      fullKernelMoment parameters 0 (firstCoordinateInjectionKernel parameters) *
        (fullKernelMoment parameters 0 (angularMeanKernel parameters 1) *
          (actualForce0BaseConstant parameters L *
            actualGaugeUnknownQABaseConstant parameters L compactRadius)) := by
    unfold actualUnknownN0Kernel
    apply (fullKernelNeg_moment_le parameters 0 _ |> fun h =>
      (fullKernelComposition_zero_moment_le _ _).trans
        (mul_le_mul_of_nonneg_left h (fullKernelMoment_nonnegative parameters 0 _))).trans
    have fq := fullKernelComposition_zero_moment_le_of _ _ _ _ force0 qABound
      (actualForce0BaseConstant_nonnegative parameters L)
      (actualGaugeUnknownQABaseConstant_nonnegative parameters L compactRadius)
    have mfq := fullKernelComposition_zero_moment_le_of
      (inputDimension := 1) (middleDimension := 1) (outputDimension := 1)
      (angularMeanKernel parameters 1)
      (fullKernelComposition
        (actualForceBoundaryKernel parameters L rho epsilon field 0 coefficientLow)
        (fullKernelComposition
          (actualGaugeQKernelOnBall parameters L rho alpha delta parameter epsilon
            compactRadius field smallSix compactNonnegative alphaSmall deltaSmall parameterSmall)
          (actualUnknownQAKernel parameters))) _ _ le_rfl fq
      (fullKernelMoment_nonnegative parameters 0 _)
      (mul_nonneg (actualForce0BaseConstant_nonnegative parameters L)
        (actualGaugeUnknownQABaseConstant_nonnegative parameters L compactRadius))
    exact mul_le_mul_of_nonneg_left mfq (fullKernelMoment_nonnegative parameters 0 _)
  have n1 : fullKernelMoment parameters 0
      (actualUnknownN1Kernel parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall
        parameterSmall) ≤
      fullKernelMoment parameters 0 (secondCoordinateInjectionKernel parameters) *
        (fullKernelMoment parameters 0
            (fullKernelSmul 2 (fullIdentityKernel parameters 1)) +
          actualRotatedForce0BaseConstant parameters L *
            actualGaugeUnknownQABaseConstant parameters L compactRadius +
          actualForce0BaseConstant parameters L *
            fullKernelMoment parameters 0 (firstCoordinateInjectionKernel parameters)) := by
    unfold actualUnknownN1Kernel
    dsimp only
    have first := fullKernelComposition_zero_moment_le_of _ _ _ _ rotatedForce0
      qABound (actualRotatedForce0BaseConstant_nonnegative parameters L)
      (actualGaugeUnknownQABaseConstant_nonnegative parameters L compactRadius)
    have second := fullKernelComposition_zero_moment_le_of
      (inputDimension := 1) (middleDimension := 3) (outputDimension := 1)
      (actualForceBoundaryKernel parameters L rho epsilon field 0 coefficientLow)
      (firstCoordinateInjectionKernel parameters) _ _ force0 le_rfl
      (actualForce0BaseConstant_nonnegative parameters L)
      (fullKernelMoment_nonnegative parameters 0 _)
    have sumBound := fullKernelAdd_zero_moment_le_of _ _ _ _ first second
    have subBound := fullKernelAdd_zero_moment_le_of
      (sourceDimension := 1) (targetDimension := 1)
      (fullKernelSmul 2 (fullIdentityKernel parameters 1))
      (fullKernelNeg
        (fullKernelAdd
          (fullKernelComposition
            (actualRotatedForceBoundaryKernel parameters L rho epsilon field 0 coefficientLow)
            (fullKernelComposition
              (actualGaugeQKernelOnBall parameters L rho alpha delta parameter epsilon
                compactRadius field smallSix compactNonnegative alphaSmall deltaSmall parameterSmall)
              (actualUnknownQAKernel parameters)))
          (fullKernelComposition
            (actualForceBoundaryKernel parameters L rho epsilon field 0 coefficientLow)
            (firstCoordinateInjectionKernel parameters)))) _ _ le_rfl
      ((fullKernelNeg_moment_le parameters 0 _).trans sumBound)
    have subBound' : fullKernelMoment parameters 0
        (fullKernelSub
          (fullKernelSmul 2 (fullIdentityKernel parameters 1))
          (fullKernelAdd
            (fullKernelComposition
              (actualRotatedForceBoundaryKernel parameters L rho epsilon field 0 coefficientLow)
              (fullKernelComposition
                (actualGaugeQKernelOnBall parameters L rho alpha delta parameter epsilon
                  compactRadius field smallSix compactNonnegative alphaSmall deltaSmall parameterSmall)
                (actualUnknownQAKernel parameters)))
            (fullKernelComposition
              (actualForceBoundaryKernel parameters L rho epsilon field 0 coefficientLow)
              (firstCoordinateInjectionKernel parameters)))) ≤
        fullKernelMoment parameters 0 (fullKernelSmul 2 (fullIdentityKernel parameters 1)) +
          actualRotatedForce0BaseConstant parameters L *
              actualGaugeUnknownQABaseConstant parameters L compactRadius +
            actualForce0BaseConstant parameters L *
              fullKernelMoment parameters 0 (firstCoordinateInjectionKernel parameters) := by
      simpa only [fullKernelSub, add_assoc] using subBound
    exact (fullKernelComposition_zero_moment_le _ _).trans
      (mul_le_mul_of_nonneg_left subBound' (fullKernelMoment_nonnegative parameters 0 _))
  have n2 : fullKernelMoment parameters 0
      (actualUnknownN2Kernel parameters L rho alpha delta parameter epsilon
        compactRadius field small compactNonnegative alphaSmall deltaSmall
        parameterSmall) ≤
      fullKernelMoment parameters 0 (thirdCoordinateInjectionKernel parameters) *
        (fullKernelMoment parameters 0 (angularMeanFreeKernel parameters 1) *
          (actualForce2BaseConstant parameters L *
            actualGaugeUnknownQABaseConstant parameters L compactRadius)) := by
    unfold actualUnknownN2Kernel
    dsimp only
    have fq := fullKernelComposition_zero_moment_le_of _ _ _ _ force2 qABound
      (actualForce2BaseConstant_nonnegative parameters L)
      (actualGaugeUnknownQABaseConstant_nonnegative parameters L compactRadius)
    have mfq := fullKernelComposition_zero_moment_le_of
      (inputDimension := 1) (middleDimension := 1) (outputDimension := 1)
      (angularMeanFreeKernel parameters 1)
      (fullKernelComposition
        (actualForceBoundaryKernel parameters L rho epsilon field 1 coefficientLow)
        (fullKernelComposition
          (actualGaugeQKernelOnBall parameters L rho alpha delta parameter epsilon
            compactRadius field smallSix compactNonnegative alphaSmall deltaSmall parameterSmall)
          (actualUnknownQAKernel parameters))) _ _ le_rfl fq
      (fullKernelMoment_nonnegative parameters 0 _)
      (mul_nonneg (actualForce2BaseConstant_nonnegative parameters L)
        (actualGaugeUnknownQABaseConstant_nonnegative parameters L compactRadius))
    have neg := (fullKernelNeg_moment_le parameters 0 _).trans mfq
    exact (fullKernelComposition_zero_moment_le _ _).trans
      (mul_le_mul_of_nonneg_left neg (fullKernelMoment_nonnegative parameters 0 _))
  have nBound : fullKernelMoment parameters 0
      (actualUnknownNKernel parameters L rho alpha delta parameter epsilon compactRadius
        field small compactNonnegative alphaSmall deltaSmall parameterSmall) ≤
      actualUnknownNBaseConstant parameters L compactRadius := by
    unfold actualUnknownNKernel actualUnknownNBaseConstant
    dsimp only
    have bound := fullKernelAdd_zero_moment_le_of _ _ _ _ n0
      (fullKernelAdd_zero_moment_le_of _ _ _ _ n1 n2)
    exact bound.trans_eq (by ring)
  have wBound : fullKernelMoment parameters 0
      (actualUnknownWKernel parameters L rho alpha delta parameter epsilon compactRadius
        field small compactNonnegative alphaSmall deltaSmall parameterSmall) ≤
      actualUnknownWBaseConstant parameters L compactRadius := by
    unfold actualUnknownWKernel actualUnknownWBaseConstant
    exact fullKernelComposition_zero_moment_le_of _ _ _ _
      (actualEncodedFirstInverseKernel_moment_zero_le parameters L rho alpha delta
        parameter epsilon compactRadius field small compactNonnegative alphaSmall
        deltaSmall parameterSmall) nBound
      (actualEncodedFirstInverseBaseConstant_nonnegative parameters)
      (actualUnknownNBaseConstant_nonnegative parameters L compactRadius)
  constructor
  · unfold actualUnknownUKernel actualUnknownUBaseConstant
    dsimp only
    have jw := fullKernelComposition_zero_moment_le_of
      (inputDimension := 1) (middleDimension := 3) (outputDimension := 3)
      (encodedJKernel parameters)
      (actualUnknownWKernel parameters L rho alpha delta parameter epsilon compactRadius
        field small compactNonnegative alphaSmall deltaSmall parameterSmall) _ _ le_rfl wBound
      (fullKernelMoment_nonnegative parameters 0 _)
      (by
        unfold actualUnknownWBaseConstant
        exact mul_nonneg (actualEncodedFirstInverseBaseConstant_nonnegative parameters)
          (actualUnknownNBaseConstant_nonnegative parameters L compactRadius))
    have sum := fullKernelAdd_zero_moment_le_of
      (sourceDimension := 1) (targetDimension := 3)
      (fullKernelComposition (encodedJKernel parameters)
        (actualUnknownWKernel parameters L rho alpha delta parameter epsilon compactRadius
          field small compactNonnegative alphaSmall deltaSmall parameterSmall))
      (actualUnknownQAKernel parameters) _ _ jw le_rfl
    exact fullKernelComposition_zero_moment_le_of
      (inputDimension := 1) (middleDimension := 3) (outputDimension := 3)
      (actualGaugeQKernelOnBall parameters L rho alpha delta parameter epsilon
        compactRadius field smallSix compactNonnegative alphaSmall deltaSmall parameterSmall)
      (fullKernelAdd
        (fullKernelComposition (encodedJKernel parameters)
          (actualUnknownWKernel parameters L rho alpha delta parameter epsilon compactRadius
            field small compactNonnegative alphaSmall deltaSmall parameterSmall))
        (actualUnknownQAKernel parameters)) _ _
      (actualGaugeQKernelOnBall_moment_zero_le parameters L rho alpha delta parameter
        epsilon compactRadius field smallSix compactNonnegative alphaSmall deltaSmall
        parameterSmall) sum
      (actualGaugeQBaseConstant_nonnegative parameters L compactRadius)
      (by
        unfold actualUnknownWBaseConstant actualUnknownQABaseConstant
        exact add_nonneg
          (mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
            (mul_nonneg (actualEncodedFirstInverseBaseConstant_nonnegative parameters)
              (actualUnknownNBaseConstant_nonnegative parameters L compactRadius)))
          (fullKernelMoment_nonnegative parameters 0 _))
  · unfold actualUnknownVKernel actualUnknownVBaseConstant
    have rw := fullKernelComposition_zero_moment_le_of
      (inputDimension := 1) (middleDimension := 3) (outputDimension := 3)
      (encodedRotationKernel parameters)
      (actualUnknownWKernel parameters L rho alpha delta parameter epsilon compactRadius
        field small compactNonnegative alphaSmall deltaSmall parameterSmall) _ _ le_rfl wBound
      (fullKernelMoment_nonnegative parameters 0 _)
      (by
        unfold actualUnknownWBaseConstant
        exact mul_nonneg (actualEncodedFirstInverseBaseConstant_nonnegative parameters)
          (actualUnknownNBaseConstant_nonnegative parameters L compactRadius))
    exact fullKernelAdd_zero_moment_le_of
      (sourceDimension := 1) (targetDimension := 3)
      (fullKernelComposition (encodedRotationKernel parameters)
        (actualUnknownWKernel parameters L rho alpha delta parameter epsilon compactRadius
          field small compactNonnegative alphaSmall deltaSmall parameterSmall))
      (firstCoordinateInjectionKernel parameters) _ _ rw le_rfl

end Grad.BoundaryKernelAction
