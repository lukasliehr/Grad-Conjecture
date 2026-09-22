import AAZ9ActualInitialWeakJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRadialJets
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem annularMode_frequency_bound (mode : HighAnnularMode) :
    |(mode.val.1 : ℝ)| ≤ Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
  unfold Grad.AnnularVariational.annularFrequency
  linarith [abs_nonneg (mode.val.2 : ℝ)]

theorem annularCell_frequency_bound (mode : HighAnnularMode) :
    |(mode.val.2 : ℝ)| ≤ Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
  unfold Grad.AnnularVariational.annularFrequency
  linarith [abs_nonneg (mode.val.1 : ℝ)]

theorem annularMode_abs_three (mode : HighAnnularMode) : (3 : ℝ) ≤ |(mode.val.1 : ℝ)| := by
  exact_mod_cast mode.property

theorem annularAngularISymbol_bound (mode : HighAnnularMode) :
    ‖annularAngularISymbol mode‖ ≤ Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
  rw [annularAngularISymbol, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact annularMode_frequency_bound mode

theorem annularDSymbol_frequency_bound (mode : HighAnnularMode) :
    ‖annularDSymbol mode‖ ≤ Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
  rw [annularDSymbol_norm]
  exact (mul_le_of_le_one_right (abs_nonneg (mode.val.1 : ℝ))
    (highMultiplier_bounds mode.val.1 (Grad.ActualReferenceAssembly.highMode_not_low _ mode.property)).2).trans
      (annularMode_frequency_bound mode)

theorem annularLongitudinalISymbol_bound (length : ℝ) (positive : 0 < length) (mode : HighAnnularMode) :
    ‖annularLongitudinalISymbol length mode‖ ≤ (1 / (3 * length ^ 2)) *
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ 2 := by
  rw [annularLongitudinalISymbol, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_mul, abs_pow, abs_pow, abs_of_pos positive]
  calc
    _ ≤ (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ 2 / (3 * length ^ 2) := by
      gcongr
      · exact annularCell_frequency_bound mode
      · exact annularMode_abs_three mode
    _ = _ := by ring

theorem annularLongitudinalSourceSymbol_bound (length : ℝ) (positive : 0 < length) (mode : HighAnnularMode) :
    ‖annularLongitudinalSourceSymbol length mode‖ ≤ (1 / (3 * length)) *
      Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
  rw [annularLongitudinalSourceSymbol, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos positive]
  calc
    _ ≤ Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 / (3 * length) := by
      gcongr
      · exact (abs_nonneg (mode.val.2 : ℝ)).trans (annularCell_frequency_bound mode)
      · exact annularCell_frequency_bound mode
      · exact annularMode_abs_three mode
    _ = _ := by ring

def annularReciprocalJetBound (lower : ℝ) (base order : ℕ) : ℝ :=
  |annularReciprocalCoefficient base order| * (lower⁻¹) ^ (base + order)

theorem annularReciprocalJetBound_nonnegative (lower : ℝ) (positive : 0 < lower) (base order : ℕ) :
    0 ≤ annularReciprocalJetBound lower base order :=
  mul_nonneg (abs_nonneg _) (pow_nonneg (inv_pos.mpr positive).le _)

theorem annularReciprocalJet_point_bound (lower : ℝ) (positive : 0 < lower) (base order : ℕ)
    (field : AnnularRawFamily lower) (mode : HighAnnularMode) :
    ‖annularReciprocalJet lower positive base order field mode‖ ≤ annularReciprocalJetBound lower base order * ‖field mode‖ := by
  change ‖annularReciprocalCoefficient base order • annularRadiusPower lower positive (base + order) (field mode)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (annularRadiusPower_bound lower positive (base + order) (field mode))
    (abs_nonneg _)).trans_eq (by unfold annularReciprocalJetBound; ring)

end Grad.AnnularRadialJets
