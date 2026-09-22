import GQC18APSmoothGauge

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope
open Grad.AnalyticWeights.Calculus Grad.AnalyticWeights.Higher

def phaseDirectional (sigma gamma ell : ℝ) (cell : ℤ) (coordinate : Fin 2) (point : SpatialPlane) : ℝ :=
  fderiv ℝ (physicalPhase sigma gamma ell cell) point (spatialBasis coordinate)

theorem phaseDirectional_smooth (sigma gamma ell : ℝ) (cell : ℤ) (coordinate : Fin 2) :
    ContDiff ℝ ∞ (phaseDirectional sigma gamma ell cell coordinate) :=
  (contDiff_infty_iff_fderiv.mp (physicalPhase_contDiff sigma gamma ell cell)).2.clm_apply contDiff_const

theorem directional_iterated_norm_le {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field) (coordinate : Fin 2) (order : ℕ) (point : SpatialPlane) :
    ‖iteratedFDeriv ℝ order (fun source => fderiv ℝ field source (spatialBasis coordinate)) point‖ ≤
      ‖iteratedFDeriv ℝ (order + 1) field point‖ := by
  let evaluation : (SpatialPlane →L[ℝ] Value) →L[ℝ] Value := ContinuousLinearMap.apply ℝ Value (spatialBasis coordinate)
  have evaluationBound : ‖evaluation‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro linear
    have basisNorm : ‖spatialBasis coordinate‖ = 1 := by
      simp [spatialBasis, PiLp.norm_single]
    simpa only [evaluation, ContinuousLinearMap.apply_apply, basisNorm, mul_one, one_mul] using linear.le_opNorm (spatialBasis coordinate)
  change ‖iteratedFDeriv ℝ order (evaluation ∘ fderiv ℝ field) point‖ ≤ _
  rw [evaluation.iteratedFDeriv_comp_left (contDiff_infty_iff_fderiv.mp smooth).2.contDiffAt
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))]
  apply (evaluation.norm_compContinuousMultilinearMap_le _).trans
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_of_le_one_left (norm_nonneg _) evaluationBound

def phaseDirectionalConstant (L gamma : ℝ) (order : ℕ) : ℝ :=
  profileConstant (order + 1) * gamma * (max 1 L) ^ (order + 1)

theorem phaseDirectionalConstant_nonnegative {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) (order : ℕ) :
    0 ≤ phaseDirectionalConstant L gamma order := by
  unfold phaseDirectionalConstant
  exact mul_nonneg (mul_nonneg (profileConstant_nonnegative _) (admissible_gamma_nonnegative admissible))
    (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)

/-- One physical derivative costs exactly one kappa, uniformly in ell.
All derivatives of the original phase are retained. -/
theorem phaseDirectional_ordered_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (cell : ℤ) (coordinate : Fin 2) (order : ℕ) (word : CartesianWord order) (point : SpatialPlane) :
    ‖orderedDerivative order word (phaseDirectional sigma gamma ell cell coordinate) point‖ ≤
      phaseDirectionalConstant L gamma order * scaledCellWeight L ell cell ^ (order + 1) := by
  have frequency := originalWidth_le_scaled L ell cell admissible.1
    (admissible_ell_nonnegative admissible) (admissible_ell_le_one admissible)
  calc
    _ ≤ ‖iteratedFDeriv ℝ order (phaseDirectional sigma gamma ell cell coordinate) point‖ := orderedDerivative_norm_le _ _ _ _
    _ ≤ ‖iteratedFDeriv ℝ (order + 1) (physicalPhase sigma gamma ell cell) point‖ :=
      directional_iterated_norm_le _ (physicalPhase_contDiff sigma gamma ell cell) coordinate order point
    _ ≤ profileConstant (order + 1) * gamma * ell ^ (order + 1) * Grad.CellWeights.cellWeight cell ^ (order + 1) :=
      physicalPhase_iterated_norm_bound sigma gamma ell cell (admissible_gamma_nonnegative admissible)
        (admissible_ell_nonnegative admissible) (order + 1) (by omega) point
    _ = (profileConstant (order + 1) * gamma) * (ell * Grad.CellWeights.cellWeight cell) ^ (order + 1) := by ring
    _ ≤ (profileConstant (order + 1) * gamma) * (max 1 L * scaledCellWeight L ell cell) ^ (order + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (admissible_ell_nonnegative admissible)
        (Grad.CellWeights.cellWeight_pos cell).le) frequency _) (mul_nonneg (profileConstant_nonnegative _)
          (admissible_gamma_nonnegative admissible))
    _ = _ := by unfold phaseDirectionalConstant; rw [mul_pow]; ring

end Grad.GaugeCoefficients.Physical.Compensated
