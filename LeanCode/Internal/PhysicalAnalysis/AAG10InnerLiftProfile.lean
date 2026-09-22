import AAG8SharpEnergyTrace
import BL6ProfileEnergy

noncomputable section
set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularVariational

open Grad.ClosedJets Grad.AnnularSourceGraph Grad.BoundaryTrace Grad.BoundaryLift

def annularInnerCutoff (lower radius : ℝ) : ℝ :=
  collarCutoff1D ((radius - lower) / (4 * (1 - lower)))

theorem annularInnerCutoff_smooth (lower : ℝ) : ContDiff ℝ ∞ (annularInnerCutoff lower) :=
  collarCutoff1D_smooth.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem annularInnerCutoff_range (lower radius : ℝ) :
    0 ≤ annularInnerCutoff lower radius ∧ annularInnerCutoff lower radius ≤ 1 :=
  collarCutoff1D_range _

theorem annularInnerCutoff_inner (lower : ℝ) : annularInnerCutoff lower lower = 1 := by
  simp only [annularInnerCutoff, sub_self, zero_div, collarCutoff1D_zero]

theorem annularInnerCutoff_vanishes (lower : ℝ) (bounded : lower < 1) (radius : ℝ)
    (far : lower + (1 - lower) / 2 ≤ radius) : annularInnerCutoff lower radius = 0 := by
  apply collarCutoff1D_vanishes
  apply (le_div_iff₀ (by positivity : 0 < 4 * (1 - lower))).2
  linarith

theorem annularInnerCutoff_outer (lower : ℝ) (bounded : lower < 1) : annularInnerCutoff lower 1 = 0 :=
  annularInnerCutoff_vanishes lower bounded 1 (by linarith)

theorem annularInnerCutoff_derivative_bound_exists (lower : ℝ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ radius ∈ Icc lower 1, |deriv (annularInnerCutoff lower) radius| ≤ bound := by
  have continuous := (contDiff_infty_iff_deriv.mp (annularInnerCutoff_smooth lower)).2.continuous
  obtain ⟨bound, bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn continuous.continuousOn
  refine ⟨max bound 0, le_max_right _ _, fun radius inside => ?_⟩
  exact (bounded radius inside).trans (le_max_left _ _)

def annularInnerCutoffDerivativeBound (lower : ℝ) : ℝ :=
  (annularInnerCutoff_derivative_bound_exists lower).choose

theorem annularInnerCutoffDerivativeBound_nonnegative (lower : ℝ) :
    0 ≤ annularInnerCutoffDerivativeBound lower :=
  (annularInnerCutoff_derivative_bound_exists lower).choose_spec.1

theorem annularInnerCutoff_derivative_bound (lower radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |deriv (annularInnerCutoff lower) radius| ≤ annularInnerCutoffDerivativeBound lower :=
  (annularInnerCutoff_derivative_bound_exists lower).choose_spec.2 radius inside

/-- The literal AG17 profile, with the sharp normalized trace coefficient. -/
def annularInnerLiftProfile (lower : ℝ) (mode : HighAnnularMode) (radius : ℝ) : ℝ :=
  annularInnerCutoff lower radius * Real.exp (-annularFrequency mode.val.1 mode.val.2 * (radius - lower)) /
    Real.sqrt (annularFrequency mode.val.1 mode.val.2)

theorem annularInnerLiftProfile_smooth (lower : ℝ) (mode : HighAnnularMode) :
    ContDiff ℝ ∞ (annularInnerLiftProfile lower mode) :=
  ((annularInnerCutoff_smooth lower).mul
    ((contDiff_const.mul (contDiff_id.sub contDiff_const)).exp)).div_const _

theorem annularInnerLiftProfile_inner (lower : ℝ) (mode : HighAnnularMode) :
    annularInnerLiftProfile lower mode lower = (Real.sqrt (annularFrequency mode.val.1 mode.val.2))⁻¹ := by
  simp only [annularInnerLiftProfile, annularInnerCutoff_inner, sub_self, mul_zero, Real.exp_zero, mul_one, one_div]

theorem annularInnerLiftProfile_outer (lower : ℝ) (bounded : lower < 1) (mode : HighAnnularMode) :
    annularInnerLiftProfile lower mode 1 = 0 := by
  rw [annularInnerLiftProfile, annularInnerCutoff_outer lower bounded, zero_mul, zero_div]

theorem annularInnerLiftProfile_deriv (lower : ℝ) (mode : HighAnnularMode) (radius : ℝ) :
    deriv (annularInnerLiftProfile lower mode) radius =
      (deriv (annularInnerCutoff lower) radius -
        annularInnerCutoff lower radius * annularFrequency mode.val.1 mode.val.2) *
      Real.exp (-annularFrequency mode.val.1 mode.val.2 * (radius - lower)) /
        Real.sqrt (annularFrequency mode.val.1 mode.val.2) := by
  have cut := ((annularInnerCutoff_smooth lower).differentiable (by simp) radius).hasDerivAt
  have exponential := (((hasDerivAt_id radius).sub_const lower).const_mul
    (-annularFrequency mode.val.1 mode.val.2)).exp
  have product := (cut.mul exponential).div_const (Real.sqrt (annularFrequency mode.val.1 mode.val.2))
  have literal := product.deriv
  change deriv (annularInnerLiftProfile lower mode) radius = _ at literal
  rw [literal]
  simp only [id_eq, mul_one]
  ring

theorem annularInnerLiftProfile_abs_bound (lower : ℝ) (mode : HighAnnularMode) (radius : ℝ) :
    |annularInnerLiftProfile lower mode radius| ≤
      Real.exp (-annularFrequency mode.val.1 mode.val.2 * (radius - lower)) /
        Real.sqrt (annularFrequency mode.val.1 mode.val.2) := by
  unfold annularInnerLiftProfile
  rw [abs_div, abs_mul, abs_of_nonneg (annularInnerCutoff_range lower radius).1,
    abs_of_pos (Real.exp_pos _), abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_left (Real.exp_pos _).le (annularInnerCutoff_range lower radius).2) (Real.sqrt_nonneg _)

theorem annularInnerLiftProfile_deriv_bound (lower : ℝ) (mode : HighAnnularMode)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |deriv (annularInnerLiftProfile lower mode) radius| ≤
      ((annularInnerCutoffDerivativeBound lower + 1) * annularFrequency mode.val.1 mode.val.2) *
        Real.exp (-annularFrequency mode.val.1 mode.val.2 * (radius - lower)) /
          Real.sqrt (annularFrequency mode.val.1 mode.val.2) := by
  rw [annularInnerLiftProfile_deriv, abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have frequencyOne := annularFrequency_one_le mode.val.1 mode.val.2
  have cutoff := annularInnerCutoff_range lower radius
  have cutDerivative := annularInnerCutoff_derivative_bound lower radius inside
  have preliminary : |deriv (annularInnerCutoff lower) radius -
      annularInnerCutoff lower radius * annularFrequency mode.val.1 mode.val.2| ≤
      |deriv (annularInnerCutoff lower) radius| +
        |annularInnerCutoff lower radius * annularFrequency mode.val.1 mode.val.2| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le (deriv (annularInnerCutoff lower) radius)
      (annularInnerCutoff lower radius * annularFrequency mode.val.1 mode.val.2)
  rw [abs_mul, abs_of_nonneg cutoff.1, abs_of_nonneg (zero_le_one.trans frequencyOne)] at preliminary
  have cutoffBound := mul_le_of_le_one_left (zero_le_one.trans frequencyOne) cutoff.2
  have absorbed := mul_le_mul_of_nonneg_left frequencyOne (annularInnerCutoffDerivativeBound_nonnegative lower)
  nlinarith only [preliminary, cutoffBound, cutDerivative, absorbed]

end Grad.AnnularVariational
