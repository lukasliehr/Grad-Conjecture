import AIX9ActualCompletedTaylorEstimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory Asymptotics
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKernelOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularKernelContinuity

section Differential
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def orbitDifferential (angular cell : E) : OrbitParameter →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight angular + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight cell

theorem orbitDifferential_apply (angular cell : E) (step : OrbitParameter) :
    orbitDifferential angular cell step = (step.1 : ℂ) • angular + (step.2 : ℂ) • cell := by
  change step.1 • angular + step.2 • cell = _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

theorem orbitStepSize_bound (step : OrbitParameter) : orbitStepSize step ≤ 2 * ‖step‖ := by
  have first := norm_fst_le step
  have second := norm_snd_le step
  rw [Real.norm_eq_abs] at first second
  unfold orbitStepSize
  linarith

/-- A proved quadratic operator remainder gives a genuine two-variable
Fréchet derivative, not only derivatives of individual Fourier entries. -/
theorem hasFDerivAt_of_orbitRemainder (function : OrbitParameter → E) (tau : OrbitParameter)
    (angular cell : E) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (remainder : ∀ step, ‖function (tau + step) - function tau -
      (step.1 : ℂ) • angular - (step.2 : ℂ) • cell‖ ≤ 3 * orbitStepSize step ^ 2 * constant) :
    HasFDerivAt function (orbitDifferential angular cell) tau := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have big : (fun step => function (tau + step) - function tau - orbitDifferential angular cell step)
      =O[𝓝 0] (fun step : OrbitParameter => ‖step‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound (12 * constant)
    apply Eventually.of_forall
    intro step
    rw [orbitDifferential_apply, sub_add_eq_sub_sub]
    apply (remainder step).trans
    have bound := pow_le_pow_left₀ (show 0 ≤ orbitStepSize step from add_nonneg (abs_nonneg _) (abs_nonneg _))
      (orbitStepSize_bound step) 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [mul_le_mul_of_nonneg_right bound nonnegative]
  exact big.trans_isLittleO (isLittleO_norm_pow_id (by norm_num : 1 < (2 : ℕ)))

end Differential

variable {src tgt : ℕ} (parameters : PhaseParameters)
    (kernel : (r : RadialPoint) → RadialKernel parameters r src tgt) (regular : RegularKernelFamily kernel)
    (power : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)

/-- Actual completed mixed jet derivatives, with the next angular and cell
jets as the derivative columns, on the SAME base DivisionRow spaces. -/
theorem radialOrbitJetAction_hasFDerivAt (tau : OrbitParameter) (angular cell : ℕ) :
    HasFDerivAt (fun sigma => radialOrbitJetAction parameters kernel regular power lower positive bounded sigma angular cell)
      (orbitDifferential
        (radialOrbitJetAction parameters kernel regular power lower positive bounded tau (angular + 1) cell)
        (radialOrbitJetAction parameters kernel regular power lower positive bounded tau angular (cell + 1))) tau := by
  obtain ⟨constant, nonnegative, bound⟩ := regular.2 (power + (angular + cell + 2))
  exact hasFDerivAt_of_orbitRemainder _ tau _ _ constant nonnegative
    (fun step => radialOrbitJetAction_remainder_bound parameters kernel regular power lower positive bounded tau step
      angular cell constant nonnegative bound)

end Grad.AnnularKernelOrbit
