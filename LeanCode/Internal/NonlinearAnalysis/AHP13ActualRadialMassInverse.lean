import AHP12UniformRadialReconstructionBound

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.SourceCollarCoefficients Grad.ActualGaugeSigmaPrimitives
open Grad.GaugeCoefficients.Physical.Allocation

def radialSigmaBaseConstant (parameters : PhaseParameters) (L : ℝ) (rotated : ℕ) : ℝ :=
  Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    ∑ component : Fin 3, sigmaScalarConstant parameters L component rotated 0

theorem radialSigmaBaseConstant_nonnegative (parameters : PhaseParameters) (L : ℝ) (rotated : ℕ) :
    0 ≤ radialSigmaBaseConstant parameters L rotated := by
  exact mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ =>
    sigmaScalarConstant_nonnegative _ _ _ _ _)

theorem radialRotatedSigmaKernel_base_bound (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (r : RadialPoint) :
    fullKernelMoment (radialKernelParameters parameters r) 0
      (radialRotatedSigmaKernel parameters L compact state r 0) ≤
        radialSigmaBaseConstant parameters L 1 *
          physicalBudget parameters state.data.field state.data.rho state.data.epsilon 6 := by
  apply (radialRowKernel_moment_le parameters r 3 0 _ _).trans
  have each (component : Fin 3) := (sigmaAngularScalarMoment_bound parameters L state.data.rho
    state.data.epsilon state.data.field state.low component 0 0 r.val r.property.1 r.property.2).2
  have summed := Finset.sum_le_sum (s := Finset.univ) fun component _ => each component
  apply (mul_le_mul_of_nonneg_left summed (Real.exp_pos _).le).trans_eq
  unfold radialSigmaBaseConstant
  simp only [← Finset.sum_mul]
  ring

def radialMassBaseConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  uniformFixedMoment parameters (fun p => angularMeanFreeKernel p 1) *
    (radialSigmaBaseConstant parameters L 1 * radialUnknownUBaseConstant parameters L compact +
      radialSigmaBaseConstant parameters L 0 * radialUnknownVBaseConstant parameters L compact)

theorem radialMassBaseConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) :
    0 ≤ radialMassBaseConstant parameters L compact := by
  unfold radialMassBaseConstant
  exact mul_nonneg (uniformFixedMoment_nonnegative _ _)
    (add_nonneg (mul_nonneg (radialSigmaBaseConstant_nonnegative _ _ _)
      (radialUnknownUBaseConstant_nonnegative _ _ _))
      (mul_nonneg (radialSigmaBaseConstant_nonnegative _ _ _)
        (radialUnknownVBaseConstant_nonnegative _ _ _)))

def radialMassLowRadius (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  min (radialFirstLowRadius parameters L compact)
    (2 * (radialMassBaseConstant parameters L compact + 1))⁻¹

theorem radialMassLowRadius_positive (parameters : PhaseParameters) (L compact : ℝ) :
    0 < radialMassLowRadius parameters L compact := by
  apply lt_min (radialFirstLowRadius_positive parameters L compact)
  apply inv_pos.mpr
  have := radialMassBaseConstant_nonnegative parameters L compact
  linarith

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialMassLowRadius parameters L compact)

theorem radialMassPerturbationKernel_bound :
    fullKernelMoment (radialKernelParameters parameters r) 0
      (radialMassPerturbationKernel parameters L compact state r (small.trans (min_le_left _ _))) ≤
        radialMassBaseConstant parameters L compact *
          physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 := by
  let budget := physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7
  have b0 : 0 ≤ budget := physicalBudget_nonnegative _ _ _ _ _
  have rotated : fullKernelMoment (radialKernelParameters parameters r) 0
      (radialRotatedSigmaKernel parameters L compact state r 0) ≤
        radialSigmaBaseConstant parameters L 1 * budget :=
    (radialRotatedSigmaKernel_base_bound parameters L compact state r).trans
      (mul_le_mul_of_nonneg_left (physicalBudget_monotone parameters state.data.field state.data.rho
        state.data.epsilon (by omega : 6 ≤ 7)) (radialSigmaBaseConstant_nonnegative _ _ _))
  have sigma : fullKernelMoment (radialKernelParameters parameters r) 0
      (radialSigmaKernel parameters L compact state r 0) ≤
        radialSigmaBaseConstant parameters L 0 * budget :=
    (radialSigmaKernel_moment_le parameters L compact state r 0 0).trans
      (mul_le_mul_of_nonneg_left (physicalBudget_monotone parameters state.data.field state.data.rho
        state.data.epsilon (by omega : 0 + 0 + 5 ≤ 7)) (radialSigmaBaseConstant_nonnegative _ _ _))
  have uv := radialUnknownUVKernel_bound parameters L compact state r (small.trans (min_le_left _ _))
  have first := fullKernelComposition_zero_moment_le_of _ _ _ _ rotated uv.1
    (mul_nonneg (radialSigmaBaseConstant_nonnegative _ _ _) b0)
    (radialUnknownUBaseConstant_nonnegative _ _ _)
  have second := fullKernelComposition_zero_moment_le_of _ _ _ _ sigma uv.2
    (mul_nonneg (radialSigmaBaseConstant_nonnegative _ _ _) b0)
    (radialUnknownVBaseConstant_nonnegative _ _ _)
  have sum := fullKernelAdd_zero_moment_le_of _ _ _ _ first second
  have mean := uniformFixedMoment_bound parameters r (fun p => angularMeanFreeKernel p 1)
    (fun first second => sameScalarModeDiagonalKernel first second _ _ _ _)
  apply (fullKernelComposition_zero_moment_le_of _ _ _ _ mean sum
    (uniformFixedMoment_nonnegative _ _) ((fullKernelMoment_nonnegative _ 0 _).trans sum)).trans_eq
  unfold radialMassBaseConstant
  ring

theorem radialMassPerturbationKernel_small :
    fullKernelMoment (radialKernelParameters parameters r) 0
      (radialMassPerturbationKernel parameters L compact state r (small.trans (min_le_left _ _))) ≤ 1 / 2 := by
  let constant := radialMassBaseConstant parameters L compact
  have C0 : 0 ≤ constant := radialMassBaseConstant_nonnegative parameters L compact
  apply ((radialMassPerturbationKernel_bound parameters L compact state r small).trans
    (mul_le_mul_of_nonneg_left (small.trans (min_le_right _ _)) C0)).trans
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by linarith : 0 < 2 * (constant + 1))).mpr
  nlinarith

def radialMassInverseKernel : RadialKernel parameters r 1 1 :=
  fullKernelNegativeIdentityInverse (radialKernelParameters parameters r)
    (radialMassPerturbationKernel parameters L compact state r (small.trans (min_le_left _ _)))
    (1 / 2) (radialMassPerturbationKernel_small parameters L compact state r small) (by norm_num)

theorem radialMassInverseKernel_twoSided :
    let mass := fullKernelNegativeIdentityPerturbation (radialKernelParameters parameters r)
      (radialMassPerturbationKernel parameters L compact state r (small.trans (min_le_left _ _)))
    let inverse := radialMassInverseKernel parameters L compact state r small
    fullKernelComposition mass inverse = fullIdentityKernel (radialKernelParameters parameters r) 1 ∧
    fullKernelComposition inverse mass = fullIdentityKernel (radialKernelParameters parameters r) 1 :=
  ⟨fullKernelNegativeIdentity_inverse_right _ _ _ _ _, fullKernelNegativeIdentity_inverse_left _ _ _ _ _⟩

end Grad.AnnularReconstruction
