import BKB44ActualUnknownBounds

noncomputable section

set_option maxHeartbeats 1800000

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualGaugeSigmaPrimitives
open Grad.GaugeCoefficients.Physical.Allocation

def actualSigmaBaseConstant (parameters : PhaseParameters) (L : ℝ) : ℝ :=
  Real.exp (parameters.sigma0 + parameters.gamma) *
    ∑ component : Fin 3, sigmaScalarConstant parameters L component 0 0

def actualRotatedSigmaBaseConstant (parameters : PhaseParameters) (L : ℝ) : ℝ :=
  Real.exp (parameters.sigma0 + parameters.gamma) *
    ∑ component : Fin 3, sigmaScalarConstant parameters L component 1 0

theorem actualSigmaBaseConstant_nonnegative (parameters : PhaseParameters) (L : ℝ) :
    0 ≤ actualSigmaBaseConstant parameters L := by
  unfold actualSigmaBaseConstant
  exact mul_nonneg (Real.exp_pos _).le
    (Finset.sum_nonneg fun component _ => sigmaScalarConstant_nonnegative
      parameters L component 0 0)

theorem actualRotatedSigmaBaseConstant_nonnegative
    (parameters : PhaseParameters) (L : ℝ) :
    0 ≤ actualRotatedSigmaBaseConstant parameters L := by
  unfold actualRotatedSigmaBaseConstant
  exact mul_nonneg (Real.exp_pos _).le
    (Finset.sum_nonneg fun component _ => sigmaScalarConstant_nonnegative
      parameters L component 1 0)

def actualMassBaseConstant (parameters : PhaseParameters)
    (L compactRadius : ℝ) : ℝ :=
  fullKernelMoment parameters 0 (angularMeanFreeKernel parameters 1) *
    (actualRotatedSigmaBaseConstant parameters L *
        actualUnknownUBaseConstant parameters L compactRadius +
      actualSigmaBaseConstant parameters L *
        actualUnknownVBaseConstant parameters L compactRadius)

theorem actualMassBaseConstant_nonnegative (parameters : PhaseParameters)
    (L compactRadius : ℝ) :
    0 ≤ actualMassBaseConstant parameters L compactRadius := by
  unfold actualMassBaseConstant
  exact mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
    (add_nonneg
      (mul_nonneg (actualRotatedSigmaBaseConstant_nonnegative parameters L)
        (actualUnknownUBaseConstant_nonnegative parameters L compactRadius))
      (mul_nonneg (actualSigmaBaseConstant_nonnegative parameters L)
        (actualUnknownVBaseConstant_nonnegative parameters L compactRadius)))

/-- AF13's one fixed low ball, with the base norm of `T_b` at most one half. -/
def actualMassInverseLowRadius (parameters : PhaseParameters)
    (L compactRadius : ℝ) : ℝ :=
  min (actualEncodedFirstLowRadius parameters L compactRadius)
    (2 * (actualMassBaseConstant parameters L compactRadius + 1))⁻¹

theorem actualMassInverseLowRadius_positive (parameters : PhaseParameters)
    (L compactRadius : ℝ) :
    0 < actualMassInverseLowRadius parameters L compactRadius := by
  unfold actualMassInverseLowRadius
  apply lt_min (actualEncodedFirstLowRadius_positive parameters L compactRadius)
  exact inv_pos.mpr (by
    linarith [actualMassBaseConstant_nonnegative parameters L compactRadius])

theorem actualMassInverseLowRadius_le_first (parameters : PhaseParameters)
    (L compactRadius : ℝ) :
    actualMassInverseLowRadius parameters L compactRadius ≤
      actualEncodedFirstLowRadius parameters L compactRadius :=
  min_le_left _ _

theorem actualMassPerturbationKernel_moment_zero_le
    (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    fullKernelMoment parameters 0
        (actualMassPerturbationKernel parameters L rho alpha delta parameter epsilon
          compactRadius field
            (small.trans (actualMassInverseLowRadius_le_first parameters L compactRadius))
          compactNonnegative alphaSmall deltaSmall parameterSmall) ≤
      actualMassBaseConstant parameters L compactRadius *
        physicalBudget parameters field rho epsilon 7 := by
  let smallFirst := small.trans
    (actualMassInverseLowRadius_le_first parameters L compactRadius)
  let smallGauge := smallFirst.trans
    (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius)
  let smallSix := (physicalBudget_monotone parameters field rho epsilon
    (by omega : 6 ≤ 7)).trans smallGauge
  let coefficientLow := smallSix.trans
    (actualGaugeInverseLowRadius_le_original parameters L compactRadius)
  have uv := actualUnknownUVKernel_moment_zero_le parameters L rho alpha delta
    parameter epsilon compactRadius field smallFirst compactNonnegative alphaSmall
    deltaSmall parameterSmall
  have sigma := actualSigmaBoundaryKernel_moment_le parameters L rho epsilon field
    coefficientLow 0
  have rotatedSigma := actualRotatedSigmaBoundaryKernel_moment_le parameters L rho
    epsilon field coefficientLow 0
  have sigma' : fullKernelMoment parameters 0
      (actualSigmaBoundaryKernel parameters L rho epsilon field coefficientLow) ≤
      actualSigmaBaseConstant parameters L *
        physicalBudget parameters field rho epsilon 7 := by
    have sigmaBase : fullKernelMoment parameters 0
        (actualSigmaBoundaryKernel parameters L rho epsilon field coefficientLow) ≤
        actualSigmaBaseConstant parameters L *
          physicalBudget parameters field rho epsilon (0 + 5) := by
      unfold actualSigmaBaseConstant
      convert sigma using 1
      rw [← Finset.sum_mul]
      ring
    exact sigmaBase.trans (mul_le_mul_of_nonneg_left
      (physicalBudget_monotone parameters field rho epsilon (by omega : 0 + 5 ≤ 7))
      (actualSigmaBaseConstant_nonnegative parameters L))
  have rotatedSigma' : fullKernelMoment parameters 0
      (actualRotatedSigmaBoundaryKernel parameters L rho epsilon field coefficientLow) ≤
      actualRotatedSigmaBaseConstant parameters L *
        physicalBudget parameters field rho epsilon 7 := by
    have rotatedSigmaBase : fullKernelMoment parameters 0
        (actualRotatedSigmaBoundaryKernel parameters L rho epsilon field coefficientLow) ≤
        actualRotatedSigmaBaseConstant parameters L *
          physicalBudget parameters field rho epsilon (0 + 6) := by
      unfold actualRotatedSigmaBaseConstant
      convert rotatedSigma using 1
      simp only [Nat.zero_add]
      rw [← Finset.sum_mul]
      ring
    exact rotatedSigmaBase.trans (mul_le_mul_of_nonneg_left
      (physicalBudget_monotone parameters field rho epsilon (by omega : 0 + 6 ≤ 7))
      (actualRotatedSigmaBaseConstant_nonnegative parameters L))
  unfold actualMassPerturbationKernel
  dsimp only
  have first := fullKernelComposition_zero_moment_le_of _ _ _ _ rotatedSigma' uv.1
    (mul_nonneg (actualRotatedSigmaBaseConstant_nonnegative parameters L)
      (physicalBudget_nonnegative parameters field rho epsilon 7))
    (actualUnknownUBaseConstant_nonnegative parameters L compactRadius)
  have second := fullKernelComposition_zero_moment_le_of _ _ _ _ sigma' uv.2
    (mul_nonneg (actualSigmaBaseConstant_nonnegative parameters L)
      (physicalBudget_nonnegative parameters field rho epsilon 7))
    (actualUnknownVBaseConstant_nonnegative parameters L compactRadius)
  have added := fullKernelAdd_zero_moment_le_of _ _ _ _ first second
  have projected := fullKernelComposition_zero_moment_le_of
    (inputDimension := 1) (middleDimension := 1) (outputDimension := 1)
    (angularMeanFreeKernel parameters 1)
    (fullKernelAdd
      (fullKernelComposition
        (actualRotatedSigmaBoundaryKernel parameters L rho epsilon field coefficientLow)
        (actualUnknownUKernel parameters L rho alpha delta parameter epsilon compactRadius
          field smallFirst compactNonnegative alphaSmall deltaSmall parameterSmall))
      (fullKernelComposition
        (actualSigmaBoundaryKernel parameters L rho epsilon field coefficientLow)
        (actualUnknownVKernel parameters L rho alpha delta parameter epsilon compactRadius
          field smallFirst compactNonnegative alphaSmall deltaSmall parameterSmall))) _ _ le_rfl added
    (fullKernelMoment_nonnegative parameters 0 _)
    (add_nonneg
      (mul_nonneg (mul_nonneg (actualRotatedSigmaBaseConstant_nonnegative parameters L)
        (physicalBudget_nonnegative parameters field rho epsilon 7))
        (actualUnknownUBaseConstant_nonnegative parameters L compactRadius))
      (mul_nonneg (mul_nonneg (actualSigmaBaseConstant_nonnegative parameters L)
        (physicalBudget_nonnegative parameters field rho epsilon 7))
        (actualUnknownVBaseConstant_nonnegative parameters L compactRadius)))
  exact projected.trans_eq (by unfold actualMassBaseConstant; ring)

theorem actualMassPerturbationKernel_moment_zero_le_half
    (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    fullKernelMoment parameters 0
        (actualMassPerturbationKernel parameters L rho alpha delta parameter epsilon
          compactRadius field
            (small.trans (actualMassInverseLowRadius_le_first parameters L compactRadius))
          compactNonnegative alphaSmall deltaSmall parameterSmall) ≤ 1 / 2 := by
  let constant := actualMassBaseConstant parameters L compactRadius
  have base := actualMassPerturbationKernel_moment_zero_le parameters L rho alpha
    delta parameter epsilon compactRadius field small compactNonnegative alphaSmall
    deltaSmall parameterSmall
  have budget : physicalBudget parameters field rho epsilon 7 ≤
      (2 * (constant + 1))⁻¹ := small.trans (min_le_right _ _)
  apply base.trans
  apply (mul_le_mul_of_nonneg_left budget
    (actualMassBaseConstant_nonnegative parameters L compactRadius)).trans
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by
    have := actualMassBaseConstant_nonnegative parameters L compactRadius
    dsimp only [constant]
    linarith : 0 < 2 * (constant + 1))).mpr
  dsimp only [constant]
  nlinarith [actualMassBaseConstant_nonnegative parameters L compactRadius]

/-- AF15's actual two-sided inverse of `-I+T_b`. -/
def actualMassInverseKernel (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius) :
    FullTwoFrequencyKernel parameters 1 1 :=
  let smallFirst := small.trans
    (actualMassInverseLowRadius_le_first parameters L compactRadius)
  let mass := actualMassPerturbationKernel parameters L rho alpha delta parameter
    epsilon compactRadius field smallFirst compactNonnegative alphaSmall deltaSmall
    parameterSmall
  fullKernelNegativeIdentityInverse parameters mass (1 / 2)
    (actualMassPerturbationKernel_moment_zero_le_half parameters L rho alpha delta
      parameter epsilon compactRadius field small compactNonnegative alphaSmall
      deltaSmall parameterSmall) (by norm_num)

end Grad.BoundaryKernelAction
