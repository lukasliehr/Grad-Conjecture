import AW3Phase
import AAG1ActualPhasePotential

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Set
open scoped ContDiff
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.PhaseAlgebra Grad.AnnularVariational
open Grad.AnalyticWeights.Calculus Grad.AnalyticWeights.Higher

def phaseRadialRay : ℝ →L[ℝ] SpatialPlane :=
  ContinuousLinearMap.toSpanSingleton ℝ (spatialBasis 0)

theorem phaseRadialRay_norm : ‖phaseRadialRay‖ = 1 := by
  simp [phaseRadialRay, ContinuousLinearMap.norm_toSpanSingleton, spatialBasis, PiLp.norm_single]

theorem radialPhase_ray (parameters : PhaseParameters) (cell : ℤ) :
    (fun radius => radialPhase parameters radius cell) =
      cartesianPhase parameters cell ∘ phaseRadialRay := by
  funext radius
  simp only [Function.comp_def, cartesianPhase_formula, phaseRadialRay,
    ContinuousLinearMap.toSpanSingleton_apply, norm_smul, Real.norm_eq_abs]
  have basisNorm : ‖spatialBasis 0‖ = 1 := by simp [spatialBasis, PiLp.norm_single]
  rw [basisNorm, mul_one, sq_abs]
  rfl

theorem radialPhase_smooth (parameters : PhaseParameters) (cell : ℤ) :
    ContDiff ℝ ∞ (fun radius => radialPhase parameters radius cell) := by
  rw [radialPhase_ray]
  exact (cartesianPhase_contDiff parameters cell).comp phaseRadialRay.contDiff

theorem annularPhaseSlope_eq_deriv (parameters : PhaseParameters) (cell : ℤ) :
    annularPhaseSlope parameters cell = deriv (fun radius => radialPhase parameters radius cell) := by
  funext radius
  exact (radialPhase_hasDerivAt parameters cell radius).deriv.symm

theorem annularPhaseSlope_smooth (parameters : PhaseParameters) (cell : ℤ) :
    ContDiff ℝ ∞ (annularPhaseSlope parameters cell) := by
  rw [annularPhaseSlope_eq_deriv]
  exact (contDiff_infty_iff_deriv.mp (radialPhase_smooth parameters cell)).2

theorem radialRay_iteratedDeriv_bound {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field)
    (rank : ℕ) (radius : ℝ) :
    ‖iteratedDeriv rank (field ∘ phaseRadialRay) radius‖ ≤
      ‖iteratedFDeriv ℝ rank field (phaseRadialRay radius)‖ := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    phaseRadialRay.iteratedFDeriv_comp_right smooth radius
      (by exact_mod_cast (le_top : (rank : ℕ∞) ≤ ⊤))]
  simpa only [phaseRadialRay_norm, Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ rank field (phaseRadialRay radius)).norm_compContinuousLinearMap_le
      (fun _ => phaseRadialRay)

theorem smoothCurve_iteratedDeriv_smooth {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (field : ℝ → Value) (smooth : ContDiff ℝ ∞ field) (rank : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv rank field) := by
  induction rank with
  | zero => simpa only [iteratedDeriv_zero] using smooth
  | succ rank previous =>
      rw [iteratedDeriv_succ]
      exact (contDiff_infty_iff_deriv.mp previous).2

theorem smoothCurve_iteratedDeriv_hasDerivAt {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (field : ℝ → Value) (smooth : ContDiff ℝ ∞ field) (rank : ℕ) (radius : ℝ) :
    HasDerivAt (iteratedDeriv rank field) (iteratedDeriv (rank + 1) field radius) radius := by
  rw [iteratedDeriv_succ]
  exact ((smoothCurve_iteratedDeriv_smooth field smooth rank).differentiable (by simp) radius).hasDerivAt

theorem radialPhase_iterated_norm_bound (parameters : PhaseParameters) (cell : ℤ)
    (rank : ℕ) (positiveRank : 1 ≤ rank) (radius : ℝ) :
    ‖iteratedDeriv rank (fun point => radialPhase parameters point cell) radius‖ ≤
      profileConstant rank * parameters.gamma * cellFrequency cell ^ rank := by
  rw [radialPhase_ray]
  apply (radialRay_iteratedDeriv_bound _ (cartesianPhase_contDiff parameters cell) rank radius).trans
  have bound := physicalPhase_iterated_norm_bound parameters.sigma0 parameters.gamma 1 cell
    parameters.gamma_pos.le (by norm_num) rank positiveRank (phaseRadialRay radius)
  change ‖iteratedFDeriv ℝ rank (physicalPhase parameters.sigma0 parameters.gamma 1 cell)
    (phaseRadialRay radius)‖ ≤ _
  simpa only [one_pow, mul_one, cellFrequency] using bound

def phaseSlopeJetConstant (parameters : PhaseParameters) (order : ℕ) : ℝ :=
  profileConstant (order + 1) * parameters.gamma

theorem phaseSlopeJetConstant_nonnegative (parameters : PhaseParameters) (order : ℕ) :
    0 ≤ phaseSlopeJetConstant parameters order :=
  mul_nonneg (profileConstant_nonnegative _) parameters.gamma_pos.le

theorem annularPhaseSlope_iterated_cell_bound (parameters : PhaseParameters) (cell : ℤ)
    (order : ℕ) (radius : ℝ) :
    ‖iteratedDeriv order (annularPhaseSlope parameters cell) radius‖ ≤
      phaseSlopeJetConstant parameters order * cellFrequency cell ^ (order + 1) := by
  rw [annularPhaseSlope_eq_deriv, ← iteratedDeriv_succ']
  exact radialPhase_iterated_norm_bound parameters cell (order + 1) (by omega) radius

theorem annularPhaseSlope_iterated_bound (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (order : ℕ) (radius : ℝ) :
    ‖iteratedDeriv order (annularPhaseSlope parameters mode.2) radius‖ ≤
      phaseSlopeJetConstant parameters order * annularFrequency mode.1 mode.2 ^ (order + 1) := by
  apply (annularPhaseSlope_iterated_cell_bound parameters mode.2 order radius).trans
  apply mul_le_mul_of_nonneg_left _ (phaseSlopeJetConstant_nonnegative parameters order)
  apply pow_le_pow_left₀ (cellFrequency_pos _).le
  apply (cellFrequency_le_polynomial mode.2).trans
  change 1 + |(mode.2 : ℝ)| ≤ 1 + |(mode.1 : ℝ)| + |(mode.2 : ℝ)|
  linarith [abs_nonneg (mode.1 : ℝ)]

end Grad.AnnularWeightedSmoothness
