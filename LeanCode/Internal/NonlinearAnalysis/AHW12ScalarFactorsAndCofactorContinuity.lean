import AHW11ActualSignedCofactorKernels

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.SourceCollarCoefficients Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives
open Grad.ActualBoundaryPrimitives Grad.AnnularKernelContinuity Grad.GaugeCoefficients.Physical.Allocation

/-- Scalar multiplication keeps the actual kernel norm, including its full phase. -/
theorem fullKernelSmul_moment_le {parameters : PhaseParameters} {input output : ℕ}
    (scalar : ℂ) (kernel : FullTwoFrequencyKernel parameters input output) (moment : ℕ) :
    fullKernelMoment parameters moment (fullKernelSmul scalar kernel) ≤ ‖scalar‖ * fullKernelMoment parameters moment kernel := by
  unfold fullKernelMoment
  calc
    _ ≤ ∑' shift, ‖scalar‖ * (boundaryCoefficientPhaseCost parameters shift *
        annularFrequency shift.1 shift.2 ^ moment * kernel.entryNorm shift) := by
      apply ((fullKernelSmul scalar kernel).moments moment).tsum_le_tsum _ ((kernel.moments moment).mul_left ‖scalar‖)
      intro shift
      have bound := mul_le_mul_of_nonneg_left (fullKernelSmul_entryNorm_le scalar kernel shift)
        (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift) (pow_nonneg (annularFrequency_pos shift).le moment))
      exact bound.trans_eq (by ring)
    _ = _ := tsum_mul_left

theorem UniformRadialKernelMoments.smul_bounded {Index : Type*} {parameters : PhaseParameters} {input output : ℕ}
    {size : Index → ℕ → ℝ}
    {family : (state : Index) → (r : RadialPoint) → RadialKernel parameters r input output}
    (bounded : UniformRadialKernelMoments parameters size family)
    (scalar : RadialPoint → ℂ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (scalarBound : ∀ r, ‖scalar r‖ ≤ constant) :
    UniformRadialKernelMoments parameters size (fun state r => fullKernelSmul (scalar r) (family state r)) := by
  intro moment
  obtain ⟨coefficient, coefficientNonnegative, bound⟩ := bounded moment
  refine ⟨constant * coefficient, mul_nonneg nonnegative coefficientNonnegative, ?_⟩
  intro state r
  apply (fullKernelSmul_moment_le (scalar r) (family state r) moment).trans
  apply (mul_le_mul_of_nonneg_right (scalarBound r) (fullKernelMoment_nonnegative _ _ _)).trans
  exact (mul_le_mul_of_nonneg_left (bound state r) nonnegative).trans_eq (mul_assoc _ _ _).symm

theorem RegularKernelFamily.radial_smul {parameters : PhaseParameters} {input output : ℕ}
    {family : (r : RadialPoint) → RadialKernel parameters r input output}
    (regular : RegularKernelFamily family) (scalar : RadialPoint → ℂ) (continuous : Continuous scalar)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (bounded : ∀ r, ‖scalar r‖ ≤ constant) :
    RegularKernelFamily (fun r => fullKernelSmul (scalar r) (family r)) := by
  refine ⟨fun shift mode => continuous.smul (regular.1 shift mode), ?_⟩
  intro moment
  obtain ⟨coefficient, coefficientNonnegative, bound⟩ := regular.2 moment
  refine ⟨constant * coefficient, mul_nonneg nonnegative coefficientNonnegative, ?_⟩
  intro r
  apply (fullKernelSmul_moment_le (scalar r) (family r) moment).trans
  exact mul_le_mul (bounded r) (bound r) (fullKernelMoment_nonnegative _ _ _) nonnegative

theorem radialPoint_norm_le_one (r : RadialPoint) : ‖(r.val : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg r.property.1]
  exact r.property.2

theorem radialCofactorJetRowKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row : Fin 3) (radial : Fin 2) (direction : Fin 3) :
    RegularKernelFamily (fun r => radialCofactorJetRowKernel parameters L compact state row radial direction r) := by
  constructor
  · intro shift mode
    exact rowMultiplicationEntry_continuous (X := RadialPoint) 3
      (fun r column frequency => radialCofactorJetScalar parameters L compact state row column radial direction r frequency)
      (radialCofactorJetScalar_continuous parameters L compact state row · radial direction ·) shift mode
  · intro moment
    obtain ⟨constant, nonnegative, bound⟩ := radialCofactorJetRowKernel_vanishingMoments parameters L compact row radial direction moment
    exact ⟨constant * state.val.errorBudget moment,
      mul_nonneg nonnegative (physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon _), bound state⟩

theorem radialCofactorJetComponentKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row column : Fin 3) (radial : Fin 2) (direction : Fin 3) :
    RegularKernelFamily (fun r => radialCofactorJetComponentKernel parameters L compact state row column radial direction r) := by
  constructor
  · intro shift mode
    exact (radialCofactorJetScalar_continuous parameters L compact state row column radial direction shift).smul continuous_const
  · intro moment
    obtain ⟨constant, nonnegative, bound⟩ := radialCofactorJetComponentKernel_vanishingMoments parameters L compact row column radial direction moment
    exact ⟨constant * state.val.errorBudget moment,
      mul_nonneg nonnegative (physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon _), bound state⟩

theorem radialSignedCofactorRowKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row : Fin 3) :
    RegularKernelFamily (fun r => radialSignedCofactorRowKernel parameters L compact state row r) :=
  (constantMatrixRadialKernel_regular parameters _ _ _).neg.add
    (radialCofactorJetRowKernel_regular parameters L compact state row 0 0)

theorem radialSignedCofactorComponentKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row column : Fin 3) :
    RegularKernelFamily (fun r => radialSignedCofactorComponentKernel parameters L compact state row column r) :=
  (fixedRadialKernel_regular parameters _ (fun _ _ => sameCircularCofactorComponentKernel _ _ row column)).add
    (radialCofactorJetComponentKernel_regular parameters L compact state row column 0 0)

end Grad.AnnularReconstruction
