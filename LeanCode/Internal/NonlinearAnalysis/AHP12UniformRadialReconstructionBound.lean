import AHP11ActualRadialMassSystem

noncomputable section
set_option maxHeartbeats 1800000

namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

theorem sameUnknownQAKernel (first second : PhaseParameters) :
    SameKernelEntries (actualUnknownQAKernel first) (actualUnknownQAKernel second) :=
  (sameConstantMatrixKernel first second _ _ _).comp
    (sameScalarModeDiagonalKernel first second _ _ _ _)

def radialFirstInverseBaseConstant (parameters : PhaseParameters) : ℝ :=
  radialNeumannBaseConstant parameters 3 * uniformFixedMoment parameters encodedD0InverseKernel

theorem radialFirstInverseBaseConstant_nonnegative (parameters : PhaseParameters) :
    0 ≤ radialFirstInverseBaseConstant parameters :=
  mul_nonneg (radialNeumannBaseConstant_nonnegative _ _) (uniformFixedMoment_nonnegative _ _)

def radialUnknownNBaseConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  let qa := radialGaugeQBaseConstant parameters L compact *
    uniformFixedMoment parameters actualUnknownQAKernel
  let first := uniformFixedMoment parameters firstCoordinateInjectionKernel *
    (uniformFixedMoment parameters (fun p => angularMeanKernel p 1) *
      (radialForceBaseConstant parameters L 0 0 * qa))
  let second := uniformFixedMoment parameters secondCoordinateInjectionKernel *
    (uniformFixedMoment parameters (fun p => fullKernelSmul 2 (fullIdentityKernel p 1)) +
      (radialForceBaseConstant parameters L 0 1 * qa +
        radialForceBaseConstant parameters L 0 0 *
          uniformFixedMoment parameters firstCoordinateInjectionKernel))
  let third := uniformFixedMoment parameters thirdCoordinateInjectionKernel *
    (uniformFixedMoment parameters (fun p => angularMeanFreeKernel p 1) *
      (radialForceBaseConstant parameters L 1 0 * qa))
  first + (second + third)

theorem radialUnknownNBaseConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) :
    0 ≤ radialUnknownNBaseConstant parameters L compact := by
  unfold radialUnknownNBaseConstant
  dsimp only
  repeat' first
    | exact uniformFixedMoment_nonnegative _ _
    | exact radialGaugeQBaseConstant_nonnegative _ _ _
    | exact radialForceBaseConstant_nonnegative _ _ _ _
    | apply add_nonneg
    | apply mul_nonneg

def radialUnknownWBaseConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  radialFirstInverseBaseConstant parameters * radialUnknownNBaseConstant parameters L compact

def radialUnknownUBaseConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  radialGaugeQBaseConstant parameters L compact *
    (uniformFixedMoment parameters encodedJKernel * radialUnknownWBaseConstant parameters L compact +
      uniformFixedMoment parameters actualUnknownQAKernel)

def radialUnknownVBaseConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  uniformFixedMoment parameters encodedRotationKernel * radialUnknownWBaseConstant parameters L compact +
    uniformFixedMoment parameters firstCoordinateInjectionKernel

theorem radialUnknownUBaseConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) :
    0 ≤ radialUnknownUBaseConstant parameters L compact := by
  unfold radialUnknownUBaseConstant radialUnknownWBaseConstant
  repeat' first
    | exact uniformFixedMoment_nonnegative _ _
    | exact radialGaugeQBaseConstant_nonnegative _ _ _
    | exact radialFirstInverseBaseConstant_nonnegative _
    | exact radialUnknownNBaseConstant_nonnegative _ _ _
    | apply add_nonneg
    | apply mul_nonneg

theorem radialUnknownVBaseConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) :
    0 ≤ radialUnknownVBaseConstant parameters L compact := by
  unfold radialUnknownVBaseConstant radialUnknownWBaseConstant
  repeat' first
    | exact uniformFixedMoment_nonnegative _ _
    | exact radialFirstInverseBaseConstant_nonnegative _
    | exact radialUnknownNBaseConstant_nonnegative _ _ _
    | apply add_nonneg
    | apply mul_nonneg

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialFirstLowRadius parameters L compact)

theorem radialEncodedFirstInverseKernel_bound :
    fullKernelMoment (radialKernelParameters parameters r) 0
      (radialEncodedFirstInverseKernel parameters L compact state r small) ≤
        radialFirstInverseBaseConstant parameters := by
  have identity : fullKernelMoment (radialKernelParameters parameters r) 0
      (radialEncodedIdentityInverseKernel parameters L compact state r small) ≤
        radialNeumannBaseConstant parameters 3 := by
    apply (fullKernelNeg_moment_le _ 0 _).trans
    apply (fullKernelNegativeIdentityInverse_moment_le _ 0 _ _ _ _).trans
    exact add_le_add
      (uniformFixedMoment_bound parameters r _ (fun first second => sameFullIdentityKernel first second 3))
      (mul_le_mul_of_nonneg_left (radialPreconditionedEncodedKernel_small parameters L compact state r small)
        (by unfold fullKernelNeumannConstant; exact tsum_nonneg fun _ => by positivity))
  exact fullKernelComposition_zero_moment_le_of _ _ _ _ identity
    (uniformFixedMoment_bound parameters r _ (fun first second => sameConstantMatrixKernel first second _ _ _))
    (radialNeumannBaseConstant_nonnegative _ _) (uniformFixedMoment_nonnegative _ _)

theorem radialUnknownNKernel_bound :
    fullKernelMoment (radialKernelParameters parameters r) 0
      (radialUnknownNKernel parameters L compact state r small) ≤
        radialUnknownNBaseConstant parameters L compact := by
  have seven : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ 1 :=
    state.small.trans ((actualMassInverseLowRadius_le_first parameters L compact).trans
      ((actualEncodedFirstLowRadius_le_gauge parameters L compact).trans
        ((actualGaugeInverseLowRadius_le_original parameters L compact).trans (min_le_left _ _))))
  have fm (kind : Fin 2) : fullKernelMoment (radialKernelParameters parameters r) 0
      (radialForceKernel parameters L compact state r kind 0) ≤ radialForceBaseConstant parameters L kind 0 :=
    (radialForceKernel_moment_le parameters L compact state r kind 0 0).trans
      ((mul_le_mul_of_nonneg_left
        ((physicalBudget_monotone parameters state.data.field state.data.rho state.data.epsilon
          (by omega : 0 + 0 + 6 ≤ 7)).trans seven)
        (radialForceBaseConstant_nonnegative parameters L kind 0)).trans_eq (mul_one _))
  have rfm : fullKernelMoment (radialKernelParameters parameters r) 0
      (radialRotatedForceKernel parameters L compact state r 0 0) ≤ radialForceBaseConstant parameters L 0 1 :=
    (radialRotatedForceKernel_moment_le parameters L compact state r 0 0 0).trans
      ((mul_le_mul_of_nonneg_left seven (radialForceBaseConstant_nonnegative _ _ _ _)).trans_eq (mul_one _))
  have fixed {input output : ℕ}
      (family : (p : PhaseParameters) → FullTwoFrequencyKernel p input output) :=
    uniformFixedMoment_nonnegative parameters family
  have qa := fullKernelComposition_zero_moment_le_of _ _ _ _
    (radialGaugeQKernel_bound parameters L compact state r (small.trans (min_le_left _ _)))
    (uniformFixedMoment_bound parameters r actualUnknownQAKernel sameUnknownQAKernel)
    (radialGaugeQBaseConstant_nonnegative _ _ _) (fixed _)
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
  have twice := uniformFixedMoment_bound parameters r (fun p => fullKernelSmul 2 (fullIdentityKernel p 1))
    (fun _ _ _ _ => rfl)
  have q0 := (fullKernelMoment_nonnegative _ 0 _).trans qa
  have firstProduct := fullKernelComposition_zero_moment_le_of _ _ _ _ (fm 0) qa
    (radialForceBaseConstant_nonnegative _ _ _ _) q0
  have firstMean := fullKernelComposition_zero_moment_le_of _ _ _ _ mean firstProduct
    (fixed _) ((fullKernelMoment_nonnegative _ 0 _).trans firstProduct)
  have first := fullKernelComposition_zero_moment_le_of _ _ _ _ i0
    ((fullKernelNeg_moment_le _ 0 _).trans firstMean)
    (fixed _) ((fullKernelMoment_nonnegative _ 0 _).trans firstMean)
  have rotated := fullKernelComposition_zero_moment_le_of _ _ _ _ rfm qa
    (radialForceBaseConstant_nonnegative _ _ _ _) q0
  have forceFirst := fullKernelComposition_zero_moment_le_of _ _ _ _ (fm 0) i0
    (radialForceBaseConstant_nonnegative _ _ _ _) (fixed _)
  have secondSum := fullKernelAdd_zero_moment_le_of _ _ _ _ rotated forceFirst
  have secondSub := fullKernelAdd_zero_moment_le_of _ _ _ _ twice
    ((fullKernelNeg_moment_le _ 0 _).trans secondSum)
  have second := fullKernelComposition_zero_moment_le_of _ _ _ _ i1 secondSub
    (fixed _) ((fullKernelMoment_nonnegative _ 0 _).trans secondSub)
  have thirdProduct := fullKernelComposition_zero_moment_le_of _ _ _ _ (fm 1) qa
    (radialForceBaseConstant_nonnegative _ _ _ _) q0
  have thirdMean := fullKernelComposition_zero_moment_le_of _ _ _ _ meanFree thirdProduct
    (fixed _) ((fullKernelMoment_nonnegative _ 0 _).trans thirdProduct)
  have third := fullKernelComposition_zero_moment_le_of _ _ _ _ i2
    ((fullKernelNeg_moment_le _ 0 _).trans thirdMean)
    (fixed _) ((fullKernelMoment_nonnegative _ 0 _).trans thirdMean)
  exact fullKernelAdd_zero_moment_le_of _ _ _ _ first
    (fullKernelAdd_zero_moment_le_of _ _ _ _ second third)

theorem radialUnknownUVKernel_bound :
    fullKernelMoment (radialKernelParameters parameters r) 0
      (radialUnknownUKernel parameters L compact state r small) ≤
        radialUnknownUBaseConstant parameters L compact ∧
    fullKernelMoment (radialKernelParameters parameters r) 0
      (radialUnknownVKernel parameters L compact state r small) ≤
        radialUnknownVBaseConstant parameters L compact := by
  have w := fullKernelComposition_zero_moment_le_of _ _ _ _
    (radialEncodedFirstInverseKernel_bound parameters L compact state r small)
    (radialUnknownNKernel_bound parameters L compact state r small)
    (radialFirstInverseBaseConstant_nonnegative _) (radialUnknownNBaseConstant_nonnegative _ _ _)
  have w0 := (fullKernelMoment_nonnegative _ 0 _).trans w
  have j := uniformFixedMoment_bound parameters r encodedJKernel sameEncodedJKernel
  have rotation := uniformFixedMoment_bound parameters r encodedRotationKernel sameEncodedRotationKernel
  have qa := uniformFixedMoment_bound parameters r actualUnknownQAKernel sameUnknownQAKernel
  have first := uniformFixedMoment_bound parameters r firstCoordinateInjectionKernel
    (fun first second => sameConstantMatrixKernel first second _ _ _)
  have decoded := fullKernelComposition_zero_moment_le_of _ _ _ _ j w
    (uniformFixedMoment_nonnegative _ _) w0
  have decodedSum := fullKernelAdd_zero_moment_le_of _ _ _ _ decoded qa
  constructor
  · exact fullKernelComposition_zero_moment_le_of _ _ _ _
      (radialGaugeQKernel_bound parameters L compact state r (small.trans (min_le_left _ _))) decodedSum
      (radialGaugeQBaseConstant_nonnegative _ _ _) ((fullKernelMoment_nonnegative _ 0 _).trans decodedSum)
  · exact fullKernelAdd_zero_moment_le_of _ _ _ _
      (fullKernelComposition_zero_moment_le_of _ _ _ _ rotation w
        (uniformFixedMoment_nonnegative _ _) w0) first

end Grad.AnnularReconstruction
