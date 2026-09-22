import AHP9UniformRadialEncodedBound

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

def radialFirstBaseConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  uniformFixedMoment parameters encodedD0InverseKernel * radialEncodedEBaseConstant parameters L compact

theorem radialFirstBaseConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) :
    0 ≤ radialFirstBaseConstant parameters L compact :=
  mul_nonneg (uniformFixedMoment_nonnegative _ _) (radialEncodedEBaseConstant_nonnegative _ _ _)

def radialFirstLowRadius (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  min (radialGaugeLowRadius parameters L compact)
    (2 * (radialFirstBaseConstant parameters L compact + 1))⁻¹

theorem radialFirstLowRadius_positive (parameters : PhaseParameters) (L compact : ℝ) :
    0 < radialFirstLowRadius parameters L compact := by
  apply lt_min (radialGaugeLowRadius_positive parameters L compact)
  apply inv_pos.mpr
  have := radialFirstBaseConstant_nonnegative parameters L compact
  linarith

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialFirstLowRadius parameters L compact)

theorem radialPreconditionedEncodedKernel_small :
    fullKernelMoment (radialKernelParameters parameters r) 0
      (fullKernelNeg (radialPreconditionedEncodedKernel parameters L compact state r
        (small.trans (min_le_left _ _)))) ≤ 1 / 2 := by
  let constant := radialFirstBaseConstant parameters L compact
  have C0 : 0 ≤ constant := radialFirstBaseConstant_nonnegative parameters L compact
  have fixed := uniformFixedMoment_bound parameters r encodedD0InverseKernel
    (fun first second => sameConstantMatrixKernel first second _ _ _)
  have actual := radialEncodedPerturbationKernel_bound parameters L compact state r
    (small.trans (min_le_left _ _))
  have bound := fullKernelComposition_zero_moment_le_of _ _ _ _ fixed actual
    (uniformFixedMoment_nonnegative _ _) ((fullKernelMoment_nonnegative _ 0 _).trans actual)
  have bound' : fullKernelMoment (radialKernelParameters parameters r) 0
      (radialPreconditionedEncodedKernel parameters L compact state r
        (small.trans (min_le_left _ _))) ≤
      constant * physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 := by
    apply bound.trans_eq
    unfold constant radialFirstBaseConstant
    ring
  have budget := small.trans (min_le_right _ _)
  apply (fullKernelNeg_moment_le _ 0 _).trans
  apply (bound'.trans (mul_le_mul_of_nonneg_left budget C0)).trans
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by linarith : 0 < 2 * (constant + 1))).mpr
  nlinarith

def radialEncodedIdentityInverseKernel : RadialKernel parameters r 3 3 :=
  fullKernelNeg (fullKernelNegativeIdentityInverse (radialKernelParameters parameters r)
    (fullKernelNeg (radialPreconditionedEncodedKernel parameters L compact state r
      (small.trans (min_le_left _ _)))) (1 / 2)
    (radialPreconditionedEncodedKernel_small parameters L compact state r small) (by norm_num))

def radialEncodedFirstInverseKernel : RadialKernel parameters r 3 3 :=
  fullKernelComposition (radialEncodedIdentityInverseKernel parameters L compact state r small)
    (encodedD0InverseKernel (radialKernelParameters parameters r))

def radialEncodedFirstSystemKernel : RadialKernel parameters r 3 3 :=
  fullKernelAdd (encodedD0Kernel (radialKernelParameters parameters r))
    (radialEncodedPerturbationKernel parameters L compact state r (small.trans (min_le_left _ _)))

theorem radialEncodedIdentityInverseKernel_right :
    fullKernelComposition
      (fullKernelAdd (fullIdentityKernel (radialKernelParameters parameters r) 3)
        (radialPreconditionedEncodedKernel parameters L compact state r (small.trans (min_le_left _ _))))
      (radialEncodedIdentityInverseKernel parameters L compact state r small) =
      fullIdentityKernel (radialKernelParameters parameters r) 3 :=
  fullKernelPositiveIdentityInverse_right _ _ _
    (radialPreconditionedEncodedKernel_small parameters L compact state r small) (by norm_num)

theorem radialEncodedIdentityInverseKernel_left :
    fullKernelComposition
      (radialEncodedIdentityInverseKernel parameters L compact state r small)
      (fullKernelAdd (fullIdentityKernel (radialKernelParameters parameters r) 3)
        (radialPreconditionedEncodedKernel parameters L compact state r (small.trans (min_le_left _ _)))) =
      fullIdentityKernel (radialKernelParameters parameters r) 3 :=
  fullKernelPositiveIdentityInverse_left _ _ _
    (radialPreconditionedEncodedKernel_small parameters L compact state r small) (by norm_num)

theorem radialEncodedFirstSystemKernel_factor :
    radialEncodedFirstSystemKernel parameters L compact state r small =
      fullKernelComposition (encodedD0Kernel (radialKernelParameters parameters r))
        (fullKernelAdd (fullIdentityKernel (radialKernelParameters parameters r) 3)
          (radialPreconditionedEncodedKernel parameters L compact state r (small.trans (min_le_left _ _)))) := by
  unfold radialEncodedFirstSystemKernel radialPreconditionedEncodedKernel
  rw [fullKernelComposition_add_inner, fullKernel_comp_identity,
    ← fullKernelComposition_assoc, encodedD0Kernel_inverse_right, fullIdentityKernel_comp]

theorem radialEncodedFirstInverseKernel_twoSided :
    fullKernelComposition (radialEncodedFirstSystemKernel parameters L compact state r small)
      (radialEncodedFirstInverseKernel parameters L compact state r small) =
      fullIdentityKernel (radialKernelParameters parameters r) 3 ∧
    fullKernelComposition (radialEncodedFirstInverseKernel parameters L compact state r small)
      (radialEncodedFirstSystemKernel parameters L compact state r small) =
      fullIdentityKernel (radialKernelParameters parameters r) 3 := by
  constructor
  · rw [radialEncodedFirstSystemKernel_factor]
    unfold radialEncodedFirstInverseKernel
    rw [fullKernelComposition_assoc, ← fullKernelComposition_assoc
      (fullKernelAdd (fullIdentityKernel (radialKernelParameters parameters r) 3) _),
      radialEncodedIdentityInverseKernel_right, fullIdentityKernel_comp,
      encodedD0Kernel_inverse_right]
  · rw [radialEncodedFirstSystemKernel_factor]
    unfold radialEncodedFirstInverseKernel
    rw [fullKernelComposition_assoc, ← fullKernelComposition_assoc
      (encodedD0InverseKernel (radialKernelParameters parameters r)),
      encodedD0Kernel_inverse_left, fullIdentityKernel_comp,
      radialEncodedIdentityInverseKernel_left]

end Grad.AnnularReconstruction
