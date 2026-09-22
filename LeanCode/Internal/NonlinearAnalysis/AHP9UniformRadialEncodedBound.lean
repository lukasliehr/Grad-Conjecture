import AHP8ActualRadialEncodedSystem

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualCurrentPrimitives
open Grad.GaugeCoefficients.Physical.Allocation

def radialForceBaseConstant (parameters : PhaseParameters) (L : ℝ)
    (kind : Fin 2) (rotated : ℕ) : ℝ :=
  3 * Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    forceFourierConstant parameters L kind rotated 0

theorem radialForceBaseConstant_nonnegative (parameters : PhaseParameters) (L : ℝ)
    (kind : Fin 2) (rotated : ℕ) :
    0 ≤ radialForceBaseConstant parameters L kind rotated := by
  exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
    (forceFourierConstant_pos _ _ _ _ _).le

def radialEncodedEBaseConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  let qj := radialGaugeQBaseConstant parameters L compact *
    uniformFixedMoment parameters encodedJKernel
  let first := uniformFixedMoment parameters firstCoordinateInjectionKernel *
    (uniformFixedMoment parameters (fun p => angularMeanKernel p 1) *
      (radialForceBaseConstant parameters L 0 0 * qj))
  let second := uniformFixedMoment parameters secondCoordinateInjectionKernel *
    (uniformFixedMoment parameters (fun p => angularMeanFreeKernel p 1) *
      (radialForceBaseConstant parameters L 0 1 * qj +
        radialForceBaseConstant parameters L 0 0 *
          uniformFixedMoment parameters encodedRotationKernel))
  let third := uniformFixedMoment parameters thirdCoordinateInjectionKernel *
    (uniformFixedMoment parameters (fun p => angularMeanFreeKernel p 1) *
      (radialForceBaseConstant parameters L 1 0 * qj))
  first + second + third

theorem radialEncodedEBaseConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) :
    0 ≤ radialEncodedEBaseConstant parameters L compact := by
  unfold radialEncodedEBaseConstant
  dsimp only
  repeat' first
    | exact uniformFixedMoment_nonnegative _ _
    | exact radialGaugeQBaseConstant_nonnegative _ _ _
    | exact radialForceBaseConstant_nonnegative _ _ _ _
    | apply add_nonneg
    | apply mul_nonneg

theorem radialEncodedPerturbationKernel_bound (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialGaugeLowRadius parameters L compact) :
    fullKernelMoment (radialKernelParameters parameters r) 0
      (radialEncodedPerturbationKernel parameters L compact state r small) ≤
        radialEncodedEBaseConstant parameters L compact *
          physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 := by
  let budget := physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7
  have budget0 : 0 ≤ budget := physicalBudget_nonnegative _ _ _ _ _
  have fm (kind : Fin 2) : fullKernelMoment (radialKernelParameters parameters r) 0
      (radialForceKernel parameters L compact state r kind 0) ≤
        radialForceBaseConstant parameters L kind 0 * budget :=
    (radialForceKernel_moment_le parameters L compact state r kind 0 0).trans
      (mul_le_mul_of_nonneg_left
        (physicalBudget_monotone parameters state.data.field state.data.rho state.data.epsilon
          (by omega : 0 + 0 + 6 ≤ 7)) (radialForceBaseConstant_nonnegative parameters L kind 0))
  have rfm : fullKernelMoment (radialKernelParameters parameters r) 0
      (radialRotatedForceKernel parameters L compact state r 0 0) ≤
        radialForceBaseConstant parameters L 0 1 * budget :=
    radialRotatedForceKernel_moment_le parameters L compact state r 0 0 0
  have q := radialGaugeQKernel_bound parameters L compact state r small
  have j := uniformFixedMoment_bound parameters r encodedJKernel sameEncodedJKernel
  have rotation := uniformFixedMoment_bound parameters r encodedRotationKernel sameEncodedRotationKernel
  have i0 := uniformFixedMoment_bound parameters r firstCoordinateInjectionKernel
    (fun first second => sameConstantMatrixKernel first second _ _ _)
  have i1 := uniformFixedMoment_bound parameters r secondCoordinateInjectionKernel
    (fun first second => sameConstantMatrixKernel first second _ _ _)
  have i2 := uniformFixedMoment_bound parameters r thirdCoordinateInjectionKernel
    (fun first second => sameConstantMatrixKernel first second _ _ _)
  have mean := uniformFixedMoment_bound parameters r (fun p => angularMeanKernel p 1)
    (fun first second => sameScalarModeDiagonalKernel first second _ _ _ _)
  have meanFree := uniformFixedMoment_bound parameters r (fun p => angularMeanFreeKernel p 1)
    (fun first second => sameScalarModeDiagonalKernel first second _ _ _ _)
  have fixed {input output : ℕ}
      (family : (p : PhaseParameters) → FullTwoFrequencyKernel p input output) :=
    uniformFixedMoment_nonnegative parameters family
  have q0 := radialGaugeQBaseConstant_nonnegative parameters L compact
  have f0 := radialForceBaseConstant_nonnegative parameters L 0 0
  have rf0 := radialForceBaseConstant_nonnegative parameters L 0 1
  have f2 := radialForceBaseConstant_nonnegative parameters L 1 0
  have qj := fullKernelComposition_zero_moment_le_of _ _ _ _ q j q0 (fixed _)
  have qj0 := mul_nonneg q0 (fixed encodedJKernel)
  have firstProduct := fullKernelComposition_zero_moment_le_of _ _ _ _ (fm 0) qj
    (mul_nonneg f0 budget0) qj0
  have firstMean := fullKernelComposition_zero_moment_le_of _ _ _ _ mean firstProduct
    (fixed _) ((fullKernelMoment_nonnegative _ 0 _).trans firstProduct)
  have first := fullKernelComposition_zero_moment_le_of _ _ _ _ i0 firstMean
    (fixed _) ((fullKernelMoment_nonnegative _ 0 _).trans firstMean)
  have rotatedProduct := fullKernelComposition_zero_moment_le_of _ _ _ _ rfm qj
    (mul_nonneg rf0 budget0) qj0
  have forceRotation := fullKernelComposition_zero_moment_le_of _ _ _ _ (fm 0) rotation
    (mul_nonneg f0 budget0) (fixed _)
  have secondSum := fullKernelAdd_zero_moment_le_of _ _ _ _ rotatedProduct forceRotation
  have secondMean := fullKernelComposition_zero_moment_le_of _ _ _ _ meanFree secondSum
    (fixed _) ((fullKernelMoment_nonnegative _ 0 _).trans secondSum)
  have second := fullKernelComposition_zero_moment_le_of _ _ _ _ i1 secondMean
    (fixed _) ((fullKernelMoment_nonnegative _ 0 _).trans secondMean)
  have thirdProduct := fullKernelComposition_zero_moment_le_of _ _ _ _ (fm 1) qj
    (mul_nonneg f2 budget0) qj0
  have thirdMean := fullKernelComposition_zero_moment_le_of _ _ _ _ meanFree thirdProduct
    (fixed _) ((fullKernelMoment_nonnegative _ 0 _).trans thirdProduct)
  have third := fullKernelComposition_zero_moment_le_of _ _ _ _ i2 thirdMean
    (fixed _) ((fullKernelMoment_nonnegative _ 0 _).trans thirdMean)
  apply (fullKernelAdd_zero_moment_le_of _ _ _ _ first
    (fullKernelAdd_zero_moment_le_of _ _ _ _ second third)).trans_eq
  unfold radialEncodedEBaseConstant
  dsimp only
  ring

end Grad.AnnularReconstruction
