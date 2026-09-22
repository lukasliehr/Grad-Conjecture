import AAQ17ActualWeightedFluxGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularOmegaGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularGrades Grad.AnnularFluxTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The original high-flux frequency, with all axial cells and both signs
of every high angular mode. -/
def annularOmega (length radius : ℝ) (mode : HighAnnularMode) : ℝ :=
  Real.sqrt (((mode.val.1 : ℝ) / radius) ^ 2 + ((mode.val.2 : ℝ) / length) ^ 2)

theorem annularOmega_nonneg (length radius : ℝ) (mode : HighAnnularMode) :
    0 ≤ annularOmega length radius mode := Real.sqrt_nonneg _

theorem annularOmega_sq (length radius : ℝ) (mode : HighAnnularMode) :
    annularOmega length radius mode ^ 2 =
      ((mode.val.1 : ℝ) / radius) ^ 2 + ((mode.val.2 : ℝ) / length) ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem annularOmega_angular (length radius : ℝ) (positive : 0 < radius) (mode : HighAnnularMode) :
    |(mode.val.1 : ℝ)| / radius ≤ annularOmega length radius mode := by
  calc
    _ = Real.sqrt (((mode.val.1 : ℝ) / radius) ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_div, abs_of_pos positive]
    _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))

theorem annularOmega_cell (length radius : ℝ) (positive : 0 < length) (mode : HighAnnularMode) :
    |(mode.val.2 : ℝ)| / length ≤ annularOmega length radius mode := by
  calc
    _ = Real.sqrt (((mode.val.2 : ℝ) / length) ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_div, abs_of_pos positive]
    _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))

theorem annularOmega_pos (length radius : ℝ) (positive : 0 < radius) (mode : HighAnnularMode) :
    0 < annularOmega length radius mode := by
  have high : (3 : ℝ) ≤ |(mode.val.1 : ℝ)| := by exact_mod_cast mode.property
  exact (div_pos (by linarith : 0 < |(mode.val.1 : ℝ)|) positive).trans_le
    (annularOmega_angular length radius positive mode)

theorem annularOmega_upper (length radius : ℝ) (lengthPositive : 0 < length)
    (radiusPositive : 0 < radius) (mode : HighAnnularMode) :
    annularOmega length radius mode ≤ |(mode.val.1 : ℝ)| / radius + |(mode.val.2 : ℝ)| / length := by
  have equality := annularOmega_sq length radius mode
  have first : ((mode.val.1 : ℝ) / radius) ^ 2 = (|(mode.val.1 : ℝ)| / radius) ^ 2 := by rw [div_pow, div_pow, sq_abs]
  have second : ((mode.val.2 : ℝ) / length) ^ 2 = (|(mode.val.2 : ℝ)| / length) ^ 2 := by rw [div_pow, div_pow, sq_abs]
  rw [first, second] at equality
  have firstNonnegative := div_nonneg (abs_nonneg (mode.val.1 : ℝ)) radiusPositive.le
  have secondNonnegative := div_nonneg (abs_nonneg (mode.val.2 : ℝ)) lengthPositive.le
  nlinarith [annularOmega_nonneg length radius mode, mul_nonneg firstNonnegative secondNonnegative]

/-- The first BF3 comparison is uniform in the inner radius. -/
theorem annularNu_le_omega (length radius : ℝ) (lengthPositive : 0 < length)
    (radiusPositive : 0 < radius) (radiusBounded : radius ≤ 1) (mode : HighAnnularMode) :
    Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ≤
      (2 + length) * annularOmega length radius mode := by
  have angular := (div_le_iff₀ radiusPositive).mp (annularOmega_angular length radius radiusPositive mode)
  have cell := (div_le_iff₀ lengthPositive).mp (annularOmega_cell length radius lengthPositive mode)
  have mBound : |(mode.val.1 : ℝ)| ≤ annularOmega length radius mode :=
    angular.trans (mul_le_of_le_one_right (annularOmega_nonneg length radius mode) radiusBounded)
  have high : (3 : ℝ) ≤ |(mode.val.1 : ℝ)| := by exact_mod_cast mode.property
  unfold Grad.AnnularVariational.annularFrequency
  linarith

/-- The reverse BF3 comparison has precisely one radial inverse factor. -/
theorem annularOmega_le_nu (length radius : ℝ) (lengthPositive : 0 < length)
    (radiusPositive : 0 < radius) (radiusBounded : radius ≤ 1) (mode : HighAnnularMode) :
    annularOmega length radius mode ≤
      (1 + length⁻¹) / radius * Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
  have upper := annularOmega_upper length radius lengthPositive radiusPositive mode
  have frequencyPositive : 0 < Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
    unfold Grad.AnnularVariational.annularFrequency
    positivity
  have mBound : |(mode.val.1 : ℝ)| ≤ Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
    unfold Grad.AnnularVariational.annularFrequency
    linarith [abs_nonneg (mode.val.2 : ℝ)]
  have nBound : |(mode.val.2 : ℝ)| ≤ Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
    unfold Grad.AnnularVariational.annularFrequency
    linarith [abs_nonneg (mode.val.1 : ℝ)]
  have radial : (1 : ℝ) ≤ radius⁻¹ := (one_le_inv₀ radiusPositive).mpr radiusBounded
  calc
    _ ≤ Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 / radius +
        Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 / length :=
      upper.trans (add_le_add (div_le_div_of_nonneg_right mBound radiusPositive.le)
        (div_le_div_of_nonneg_right nBound lengthPositive.le))
    _ ≤ Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 / radius +
        Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 / length * radius⁻¹ :=
      add_le_add le_rfl (le_mul_of_one_le_right (div_nonneg frequencyPositive.le lengthPositive.le) radial)
    _ = _ := by ring

end Grad.AnnularOmegaGraph
