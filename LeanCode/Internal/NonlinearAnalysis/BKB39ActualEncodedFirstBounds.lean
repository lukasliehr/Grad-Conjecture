import BKB38GaugeMomentBounds

noncomputable section

set_option maxHeartbeats 1800000

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualCurrentPrimitives

theorem fullKernelComposition_zero_moment_le_of
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters}
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (outerBound innerBound : ℝ)
    (outerLe : fullKernelMoment parameters 0 outer ≤ outerBound)
    (innerLe : fullKernelMoment parameters 0 inner ≤ innerBound)
    (outerBoundNonnegative : 0 ≤ outerBound)
    (_innerBoundNonnegative : 0 ≤ innerBound) :
    fullKernelMoment parameters 0 (fullKernelComposition outer inner) ≤
      outerBound * innerBound :=
  (fullKernelComposition_zero_moment_le outer inner).trans
    (mul_le_mul outerLe innerLe (fullKernelMoment_nonnegative parameters 0 inner)
      outerBoundNonnegative)

theorem fullKernelAdd_zero_moment_le_of
    {sourceDimension targetDimension : ℕ} {parameters : PhaseParameters}
    (first second : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (firstBound secondBound : ℝ)
    (firstLe : fullKernelMoment parameters 0 first ≤ firstBound)
    (secondLe : fullKernelMoment parameters 0 second ≤ secondBound) :
    fullKernelMoment parameters 0 (fullKernelAdd first second) ≤
      firstBound + secondBound :=
  (fullKernelAdd_moment_le parameters 0 first second).trans
    (add_le_add firstLe secondLe)

def actualForce0BaseConstant (parameters : PhaseParameters) (L : ℝ) : ℝ :=
  3 * Real.exp (parameters.sigma0 + parameters.gamma) *
    forceFourierConstant parameters L 0 0 0

def actualRotatedForce0BaseConstant (parameters : PhaseParameters) (L : ℝ) : ℝ :=
  3 * Real.exp (parameters.sigma0 + parameters.gamma) *
    forceFourierConstant parameters L 0 1 0

def actualForce2BaseConstant (parameters : PhaseParameters) (L : ℝ) : ℝ :=
  3 * Real.exp (parameters.sigma0 + parameters.gamma) *
    forceFourierConstant parameters L 1 0 0

theorem actualForce0BaseConstant_nonnegative (parameters : PhaseParameters) (L : ℝ) :
    0 ≤ actualForce0BaseConstant parameters L := by
  unfold actualForce0BaseConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
    (forceFourierConstant_pos parameters L 0 0 0).le

theorem actualRotatedForce0BaseConstant_nonnegative
    (parameters : PhaseParameters) (L : ℝ) :
    0 ≤ actualRotatedForce0BaseConstant parameters L := by
  unfold actualRotatedForce0BaseConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
    (forceFourierConstant_pos parameters L 0 1 0).le

theorem actualForce2BaseConstant_nonnegative (parameters : PhaseParameters) (L : ℝ) :
    0 ≤ actualForce2BaseConstant parameters L := by
  unfold actualForce2BaseConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
    (forceFourierConstant_pos parameters L 1 0 0).le

theorem actualGaugeDecodedKernel_moment_zero_le (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    fullKernelMoment parameters 0
        (actualGaugeDecodedKernel parameters L rho alpha delta parameter epsilon
          compactRadius field small compactNonnegative alphaSmall deltaSmall
          parameterSmall) ≤
      actualGaugeQBaseConstant parameters L compactRadius *
        fullKernelMoment parameters 0 (encodedJKernel parameters) := by
  exact fullKernelComposition_zero_moment_le_of _ _ _ _
    (actualGaugeQKernelOnBall_moment_zero_le parameters L rho alpha delta parameter
      epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
      parameterSmall) le_rfl
    (actualGaugeQBaseConstant_nonnegative parameters L compactRadius)
    (fullKernelMoment_nonnegative parameters 0 _)

def actualEncodedEBaseConstant (parameters : PhaseParameters)
    (L compactRadius : ℝ) : ℝ :=
  let qj := actualGaugeQBaseConstant parameters L compactRadius *
    fullKernelMoment parameters 0 (encodedJKernel parameters)
  let first := fullKernelMoment parameters 0 (firstCoordinateInjectionKernel parameters) *
    (fullKernelMoment parameters 0 (angularMeanKernel parameters 1) *
      (actualForce0BaseConstant parameters L * qj))
  let second := fullKernelMoment parameters 0 (secondCoordinateInjectionKernel parameters) *
    (fullKernelMoment parameters 0 (angularMeanFreeKernel parameters 1) *
      (actualRotatedForce0BaseConstant parameters L * qj +
        actualForce0BaseConstant parameters L *
          fullKernelMoment parameters 0 (encodedRotationKernel parameters)))
  let third := fullKernelMoment parameters 0 (thirdCoordinateInjectionKernel parameters) *
    (fullKernelMoment parameters 0 (angularMeanFreeKernel parameters 1) *
      (actualForce2BaseConstant parameters L * qj))
  first + second + third

theorem actualEncodedEBaseConstant_nonnegative (parameters : PhaseParameters)
    (L compactRadius : ℝ) :
    0 ≤ actualEncodedEBaseConstant parameters L compactRadius := by
  unfold actualEncodedEBaseConstant
  dsimp only
  have qNonnegative : 0 ≤ actualGaugeQBaseConstant parameters L compactRadius :=
    actualGaugeQBaseConstant_nonnegative parameters L compactRadius
  have f0 := actualForce0BaseConstant_nonnegative parameters L
  have rf0 := actualRotatedForce0BaseConstant_nonnegative parameters L
  have f2 := actualForce2BaseConstant_nonnegative parameters L
  have qjNonnegative : 0 ≤ actualGaugeQBaseConstant parameters L compactRadius *
      fullKernelMoment parameters 0 (encodedJKernel parameters) :=
    mul_nonneg qNonnegative (fullKernelMoment_nonnegative parameters 0 _)
  apply add_nonneg
  · apply add_nonneg
    · exact mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
        (mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
          (mul_nonneg f0 qjNonnegative))
    · exact mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
        (mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
          (add_nonneg (mul_nonneg rf0 qjNonnegative)
            (mul_nonneg f0 (fullKernelMoment_nonnegative parameters 0 _))))
  · exact mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
      (mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
        (mul_nonneg f2 qjNonnegative))

theorem actualEncodedPerturbationKernel_moment_zero_le
    (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    fullKernelMoment parameters 0
        (actualEncodedPerturbationKernel parameters L rho alpha delta parameter
          epsilon compactRadius field
            ((physicalBudget_monotone parameters field rho epsilon
              (by omega : 6 ≤ 7)).trans small)
            compactNonnegative alphaSmall deltaSmall parameterSmall) ≤
      actualEncodedEBaseConstant parameters L compactRadius *
        physicalBudget parameters field rho epsilon 7 := by
  let smallSix := (physicalBudget_monotone parameters field rho epsilon
    (by omega : 6 ≤ 7)).trans small
  let coefficientLow := smallSix.trans
    (actualGaugeInverseLowRadius_le_original parameters L compactRadius)
  let qjBound := actualGaugeQBaseConstant parameters L compactRadius *
    fullKernelMoment parameters 0 (encodedJKernel parameters)
  have qj : fullKernelMoment parameters 0
      (actualGaugeDecodedKernel parameters L rho alpha delta parameter epsilon
        compactRadius field smallSix compactNonnegative alphaSmall deltaSmall
        parameterSmall) ≤ qjBound :=
    actualGaugeDecodedKernel_moment_zero_le parameters L rho alpha delta parameter
      epsilon compactRadius field smallSix compactNonnegative alphaSmall deltaSmall
      parameterSmall
  have force0 : fullKernelMoment parameters 0
      (actualForceBoundaryKernel parameters L rho epsilon field 0 coefficientLow) ≤
      actualForce0BaseConstant parameters L *
        physicalBudget parameters field rho epsilon 7 := by
    have raw := actualForceBoundaryKernel_moment_le parameters L rho epsilon field 0
      coefficientLow 0
    change _ ≤ actualForce0BaseConstant parameters L *
      physicalBudget parameters field rho epsilon (0 + 6) at raw
    exact raw.trans (mul_le_mul_of_nonneg_left
      (physicalBudget_monotone parameters field rho epsilon (by omega : 0 + 6 ≤ 7))
      (actualForce0BaseConstant_nonnegative parameters L))
  have rotatedForce0 : fullKernelMoment parameters 0
      (actualRotatedForceBoundaryKernel parameters L rho epsilon field 0 coefficientLow) ≤
      actualRotatedForce0BaseConstant parameters L *
        physicalBudget parameters field rho epsilon 7 := by
    have raw := actualRotatedForceBoundaryKernel_moment_le parameters L rho epsilon
      field 0 coefficientLow 0
    change _ ≤ actualRotatedForce0BaseConstant parameters L *
      physicalBudget parameters field rho epsilon (0 + 7) at raw
    simpa only [zero_add] using raw
  have force2 : fullKernelMoment parameters 0
      (actualForceBoundaryKernel parameters L rho epsilon field 1 coefficientLow) ≤
      actualForce2BaseConstant parameters L *
        physicalBudget parameters field rho epsilon 7 := by
    have raw := actualForceBoundaryKernel_moment_le parameters L rho epsilon field 1
      coefficientLow 0
    change _ ≤ actualForce2BaseConstant parameters L *
      physicalBudget parameters field rho epsilon (0 + 6) at raw
    exact raw.trans (mul_le_mul_of_nonneg_left
      (physicalBudget_monotone parameters field rho epsilon (by omega : 0 + 6 ≤ 7))
      (actualForce2BaseConstant_nonnegative parameters L))
  have budgetNonnegative := physicalBudget_nonnegative parameters field rho epsilon 7
  have qjBoundNonnegative : 0 ≤ qjBound := by
    dsimp only [qjBound]
    exact mul_nonneg (actualGaugeQBaseConstant_nonnegative parameters L compactRadius)
      (fullKernelMoment_nonnegative parameters 0 _)
  have e0 : fullKernelMoment parameters 0
      (actualEncodedE0Kernel parameters L rho alpha delta parameter epsilon
        compactRadius field smallSix compactNonnegative alphaSmall deltaSmall
        parameterSmall) ≤
      (fullKernelMoment parameters 0 (firstCoordinateInjectionKernel parameters) *
        (fullKernelMoment parameters 0 (angularMeanKernel parameters 1) *
          (actualForce0BaseConstant parameters L * qjBound))) *
        physicalBudget parameters field rho epsilon 7 := by
    unfold actualEncodedE0Kernel
    have forceQ := fullKernelComposition_zero_moment_le_of
      (actualForceBoundaryKernel parameters L rho epsilon field 0 coefficientLow)
      (actualGaugeDecodedKernel parameters L rho alpha delta parameter epsilon
        compactRadius field smallSix compactNonnegative alphaSmall deltaSmall
        parameterSmall) _ _ force0 qj
        (mul_nonneg (actualForce0BaseConstant_nonnegative parameters L)
          budgetNonnegative) qjBoundNonnegative
    have meanForceQ := fullKernelComposition_zero_moment_le_of
      (angularMeanKernel parameters 1) _ _ _ le_rfl forceQ
        (fullKernelMoment_nonnegative parameters 0 _)
        (mul_nonneg (mul_nonneg (actualForce0BaseConstant_nonnegative parameters L)
          budgetNonnegative) qjBoundNonnegative)
    have injected := fullKernelComposition_zero_moment_le_of
      (firstCoordinateInjectionKernel parameters) _ _ _ le_rfl meanForceQ
        (fullKernelMoment_nonnegative parameters 0 _)
        (mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
          (mul_nonneg (mul_nonneg (actualForce0BaseConstant_nonnegative parameters L)
            budgetNonnegative) qjBoundNonnegative))
    exact injected.trans_eq (by ring)
  have e1 : fullKernelMoment parameters 0
      (actualEncodedE1Kernel parameters L rho alpha delta parameter epsilon
        compactRadius field smallSix compactNonnegative alphaSmall deltaSmall
        parameterSmall) ≤
      (fullKernelMoment parameters 0 (secondCoordinateInjectionKernel parameters) *
        (fullKernelMoment parameters 0 (angularMeanFreeKernel parameters 1) *
          (actualRotatedForce0BaseConstant parameters L * qjBound +
            actualForce0BaseConstant parameters L *
              fullKernelMoment parameters 0 (encodedRotationKernel parameters)))) *
        physicalBudget parameters field rho epsilon 7 := by
    unfold actualEncodedE1Kernel
    have first := fullKernelComposition_zero_moment_le_of
      (actualRotatedForceBoundaryKernel parameters L rho epsilon field 0 coefficientLow)
      (actualGaugeDecodedKernel parameters L rho alpha delta parameter epsilon
        compactRadius field smallSix compactNonnegative alphaSmall deltaSmall
        parameterSmall) _ _ rotatedForce0 qj
        (mul_nonneg (actualRotatedForce0BaseConstant_nonnegative parameters L)
          budgetNonnegative) qjBoundNonnegative
    have second := fullKernelComposition_zero_moment_le_of
      (actualForceBoundaryKernel parameters L rho epsilon field 0 coefficientLow)
      (encodedRotationKernel parameters) _ _ force0 le_rfl
        (mul_nonneg (actualForce0BaseConstant_nonnegative parameters L)
          budgetNonnegative) (fullKernelMoment_nonnegative parameters 0 _)
    have added := fullKernelAdd_zero_moment_le_of _ _ _ _ first second
    have meanAdded := fullKernelComposition_zero_moment_le_of
      (angularMeanFreeKernel parameters 1) _ _ _ le_rfl added
        (fullKernelMoment_nonnegative parameters 0 _)
        (add_nonneg
          (mul_nonneg (mul_nonneg
            (actualRotatedForce0BaseConstant_nonnegative parameters L)
            budgetNonnegative) qjBoundNonnegative)
          (mul_nonneg (mul_nonneg (actualForce0BaseConstant_nonnegative parameters L)
            budgetNonnegative) (fullKernelMoment_nonnegative parameters 0 _)))
    have injected := fullKernelComposition_zero_moment_le_of
      (secondCoordinateInjectionKernel parameters) _ _ _ le_rfl meanAdded
        (fullKernelMoment_nonnegative parameters 0 _)
        (mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
          (add_nonneg
            (mul_nonneg (mul_nonneg
              (actualRotatedForce0BaseConstant_nonnegative parameters L)
              budgetNonnegative) qjBoundNonnegative)
            (mul_nonneg (mul_nonneg (actualForce0BaseConstant_nonnegative parameters L)
              budgetNonnegative) (fullKernelMoment_nonnegative parameters 0 _))))
    exact injected.trans_eq (by ring)
  have e2 : fullKernelMoment parameters 0
      (actualEncodedE2Kernel parameters L rho alpha delta parameter epsilon
        compactRadius field smallSix compactNonnegative alphaSmall deltaSmall
        parameterSmall) ≤
      (fullKernelMoment parameters 0 (thirdCoordinateInjectionKernel parameters) *
        (fullKernelMoment parameters 0 (angularMeanFreeKernel parameters 1) *
          (actualForce2BaseConstant parameters L * qjBound))) *
        physicalBudget parameters field rho epsilon 7 := by
    unfold actualEncodedE2Kernel
    have forceQ := fullKernelComposition_zero_moment_le_of
      (actualForceBoundaryKernel parameters L rho epsilon field 1 coefficientLow)
      (actualGaugeDecodedKernel parameters L rho alpha delta parameter epsilon
        compactRadius field smallSix compactNonnegative alphaSmall deltaSmall
        parameterSmall) _ _ force2 qj
        (mul_nonneg (actualForce2BaseConstant_nonnegative parameters L)
          budgetNonnegative) qjBoundNonnegative
    have meanForceQ := fullKernelComposition_zero_moment_le_of
      (angularMeanFreeKernel parameters 1) _ _ _ le_rfl forceQ
        (fullKernelMoment_nonnegative parameters 0 _)
        (mul_nonneg (mul_nonneg (actualForce2BaseConstant_nonnegative parameters L)
          budgetNonnegative) qjBoundNonnegative)
    have injected := fullKernelComposition_zero_moment_le_of
      (thirdCoordinateInjectionKernel parameters) _ _ _ le_rfl meanForceQ
        (fullKernelMoment_nonnegative parameters 0 _)
        (mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
          (mul_nonneg (mul_nonneg (actualForce2BaseConstant_nonnegative parameters L)
            budgetNonnegative) qjBoundNonnegative))
    exact injected.trans_eq (by ring)
  unfold actualEncodedPerturbationKernel actualEncodedEBaseConstant
  dsimp only [qjBound]
  exact (fullKernelAdd_zero_moment_le_of _ _ _ _ e0
    (fullKernelAdd_zero_moment_le_of _ _ _ _ e1 e2)).trans_eq (by ring)

end Grad.BoundaryKernelAction
