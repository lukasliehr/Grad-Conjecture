import AAQ1SharpWeakEndpoint
import AAR18NormalizedSecondRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFluxTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.WeightedTrace

def annularFluxPotentialConstant (lower length : ℝ) : ℝ :=
  Real.sqrt (annularPotentialUpperConstant lower length)

theorem annularFluxPotentialConstant_nonnegative (lower length : ℝ) :
    0 ≤ annularFluxPotentialConstant lower length := Real.sqrt_nonneg _

theorem annularFrequency_pos (mode : HighAnnularMode) :
    0 < Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := zero_lt_one.trans_le (annularFrequency_one_le _ _)

theorem annularFrequency_inverse_le (mode : HighAnnularMode) :
    (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ ≤ 1 := by
  simpa only [inv_one] using inv_anti₀ zero_lt_one (annularFrequency_one_le mode.val.1 mode.val.2)

def annularFrequencyCurve (mode : HighAnnularMode) (coefficient : C(ℝ, ℝ)) : C(ℝ, ℝ) :=
  (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ • coefficient

theorem annularFrequencyCurve_apply (mode : HighAnnularMode) (coefficient : C(ℝ, ℝ)) (radius : ℝ) :
    annularFrequencyCurve mode coefficient radius =
      coefficient radius / Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
  change (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ * coefficient radius = _
  ring

theorem annularNormalizedPotential_bound (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |annularFrequencyCurve mode (annularPotentialWeight lower length positive mode.val.1 mode.val.2) radius| ≤
      annularFluxPotentialConstant lower length := by
  have rootPositive := annularPotentialWeight_pos lower length positive mode radius
  have rootSq := annularPotentialWeight_sq lower length positive mode.val.1 mode.val.2 radius inside.1
  have upper := annularPotential_upper lower length positive mode radius inside
  have constantNonnegative : 0 ≤ annularPotentialUpperConstant lower length := by
    unfold annularPotentialUpperConstant
    positivity
  have constantSq := Real.sq_sqrt constantNonnegative
  have frequencyPositive := annularFrequency_pos mode
  have rootBound : annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius ≤
      annularFluxPotentialConstant lower length * Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
    have nonnegative := annularFluxPotentialConstant_nonnegative lower length
    change Real.sqrt (annularPotentialUpperConstant lower length) ^ 2 = _ at constantSq
    dsimp only [annularFluxPotentialConstant] at nonnegative ⊢
    apply (sq_le_sq₀ rootPositive.le (mul_nonneg nonnegative frequencyPositive.le)).mp
    rw [mul_pow, constantSq, rootSq]
    exact upper
  rw [annularFrequencyCurve_apply, abs_of_pos (div_pos rootPositive frequencyPositive)]
  exact (div_le_iff₀ frequencyPositive).2 rootBound

theorem annularNormalizedPhase_bound (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |annularFrequencyCurve mode (annularPhaseCurve parameters mode.val.2) radius| ≤
      annularFluxPotentialConstant lower length := by
  have slope := annularPhaseSlope_dominated parameters length radius mode.val.1 mode.val.2
    lengthPositive (positive.trans_le inside.1) inside.2 mode.property widthHalf widthLength
  have rootPositive := annularPotentialWeight_pos lower length positive mode radius
  have rootSq := annularPotentialWeight_sq lower length positive mode.val.1 mode.val.2 radius inside.1
  have slopeBound : |annularPhaseSlope parameters mode.val.2 radius| ≤
      annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius := by
    nlinarith [sq_abs (annularPhaseSlope parameters mode.val.2 radius)]
  have potential := annularNormalizedPotential_bound lower length positive mode radius inside
  rw [annularFrequencyCurve_apply, abs_div, abs_of_pos (annularFrequency_pos mode)] at potential ⊢
  rw [abs_of_pos rootPositive] at potential
  exact (div_le_div_of_nonneg_right slopeBound (annularFrequency_pos mode).le).trans potential

theorem annularNormalizedInverseRadius_bound (lower : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (radius : ℝ) (_inside : radius ∈ Icc lower 1) :
    |annularFrequencyCurve mode (annularInverseRadiusCurve lower positive) radius| ≤ lower⁻¹ := by
  have maxPositive := positive.trans_le (le_max_left lower radius)
  have radiusBound : 1 / max lower radius ≤ lower⁻¹ := by
    simpa only [one_div] using inv_anti₀ positive (le_max_left lower radius)
  change |(Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ * (1 / max lower radius)| ≤ _
  rw [abs_of_pos (mul_pos (inv_pos.mpr (annularFrequency_pos mode)) (one_div_pos.mpr maxPositive))]
  exact (mul_le_mul_of_nonneg_right (annularFrequency_inverse_le mode) (one_div_pos.mpr maxPositive).le).trans
    (by simpa only [one_mul] using radiusBound)

def annularInverseSquareCurve (lower : ℝ) (positive : 0 < lower) : C(ℝ, ℝ) :=
  (4 : ℝ) • (annularInverseRadiusCurve lower positive * annularInverseRadiusCurve lower positive)

theorem annularNormalizedInverseSquare_bound (lower : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (radius : ℝ) (_inside : radius ∈ Icc lower 1) :
    |annularFrequencyCurve mode (annularInverseSquareCurve lower positive) radius| ≤ 4 * lower⁻¹ ^ 2 := by
  have maxPositive := positive.trans_le (le_max_left lower radius)
  have radiusBound : 1 / max lower radius ≤ lower⁻¹ := by
    simpa only [one_div] using inv_anti₀ positive (le_max_left lower radius)
  have squared := mul_self_le_mul_self (one_div_pos.mpr maxPositive).le radiusBound
  have frequency := annularFrequency_inverse_le mode
  have frequencyPositive := annularFrequency_pos mode
  change |(Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ *
    (4 * ((1 / max lower radius) * (1 / max lower radius)))| ≤ _
  rw [abs_of_nonneg (by positivity)]
  calc
    _ ≤ 1 * (4 * ((1 / max lower radius) * (1 / max lower radius))) :=
      mul_le_mul_of_nonneg_right frequency (by positivity)
    _ ≤ _ := by nlinarith

theorem annularNormalizedD_bound (mode : HighAnnularMode) :
    ‖((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ : ℝ) • annularDSymbol mode‖ ≤ 1 := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (annularFrequency_pos mode).le), annularDSymbol_norm]
  have multiplier := mul_le_of_le_one_right (abs_nonneg (mode.val.1 : ℝ)) (highMultiplier_one_le mode.val.1)
  have frequency : |(mode.val.1 : ℝ)| ≤ Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
    unfold Grad.AnnularVariational.annularFrequency
    linarith [abs_nonneg (mode.val.2 : ℝ)]
  calc
    _ ≤ (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ * Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 :=
      mul_le_mul_of_nonneg_left (multiplier.trans frequency) (inv_nonneg.mpr (annularFrequency_pos mode).le)
    _ = 1 := inv_mul_cancel₀ (annularFrequency_pos mode).ne'

theorem annularNormalizedCell_bound (length : ℝ) (lengthPositive : 0 < length) (mode : HighAnnularMode) :
    ‖((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ : ℝ) • annularCellSymbol length mode‖ ≤ length⁻¹ := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (annularFrequency_pos mode).le), annularCellSymbol,
    norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos lengthPositive, abs_of_nonneg (highMultiplier_nonnegative _)]
  have multiplier := mul_le_of_le_one_left (abs_nonneg (mode.val.2 : ℝ)) (highMultiplier_one_le mode.val.1)
  have frequency : |(mode.val.2 : ℝ)| ≤ Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
    unfold Grad.AnnularVariational.annularFrequency
    linarith [abs_nonneg (mode.val.1 : ℝ)]
  calc
    _ ≤ (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ *
        (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 / length) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (multiplier.trans frequency) lengthPositive.le)
        (inv_nonneg.mpr (annularFrequency_pos mode).le)
    _ = length⁻¹ := by
      have nonzero := (annularFrequency_pos mode).ne'
      field_simp

end Grad.AnnularFluxTrace
