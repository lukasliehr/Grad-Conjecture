import AIA2LiteralRadialCrossTerm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularCircularForm
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularCurrentEnergy
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Zero inner energy trace is the zero endpoint of the SAME actual radial representative. -/
theorem annularEnergy_inner_radial_zero (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length) (test : annularEnergySpace lower length positive)
    (zero : annularEnergyTrace lower length positive bounded lengthPositive 0 test = 0) (mode : HighAnnularMode) :
    weightedRadialTrace 1 lower positive bounded 0 (annularModeRadialH1 lower length positive mode test) = 0 := by
  have equality := congrArg (fun boundary : AnnularBoundary => boundary mode) zero
  rw [annularEnergyTrace_eq_radial] at equality
  change (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • _ = 0 at equality
  have nonzero : (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (zero_lt_one.trans_le (annularFrequency_one_le _ _))).ne'
  exact (smul_eq_zero.mp equality).resolve_left nonzero

/-- Literal modewise factor two from the stored outer coordinate sqrt(2)w(1). -/
theorem annularEnergy_outer_inner (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : HighAnnularMode) (test field : annularEnergySpace lower length positive) :
    inner ℂ (annularEnergyOuter lower length positive test mode) (annularEnergyOuter lower length positive field mode) =
      2 * inner ℂ (weightedRadialTrace 1 lower positive bounded 1 (annularModeRadialH1 lower length positive mode test))
        (weightedRadialTrace 1 lower positive bounded 1 (annularModeRadialH1 lower length positive mode field)) := by
  rw [annularEnergyOuter_eq_trace lower length positive bounded mode test,
    annularEnergyOuter_eq_trace lower length positive bounded mode field, inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal]
  have square : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [← mul_assoc, square]

/-- Summing the genuine radial cross term yields exactly the original outer form when the TEST has zero inner trace. -/
theorem annularEnergy_cross_innerZero (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length) (test field : annularEnergySpace lower length positive)
    (zero : annularEnergyTrace lower length positive bounded lengthPositive 0 test = 0) :
    2 * (inner ℂ (annularEnergyDerivative lower length positive test) (highEnergyRadius lower length positive field) +
      inner ℂ (highEnergyRadius lower length positive test) (annularEnergyDerivative lower length positive field)) =
      inner ℂ (annularEnergyOuter lower length positive test) (annularEnergyOuter lower length positive field) := by
  have first := lp.summable_inner (𝕜 := ℂ) (annularEnergyDerivative lower length positive test)
    (highEnergyRadius lower length positive field)
  have second := lp.summable_inner (𝕜 := ℂ) (highEnergyRadius lower length positive test)
    (annularEnergyDerivative lower length positive field)
  simp only [lp.inner_eq_tsum]
  rw [← first.tsum_add second, ← tsum_mul_left]
  apply tsum_congr
  intro mode
  rw [annularEnergy_mode_cross lower length positive bounded mode test field,
    annularEnergy_inner_radial_zero lower length positive bounded lengthPositive test zero mode, inner_zero_left, sub_zero,
    annularEnergy_outer_inner lower length positive bounded mode test field]

end Grad.AnnularCircularForm
