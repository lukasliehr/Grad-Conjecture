import AAG5ActualEnergyCoordinates

noncomputable section
set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularVariational

open Grad.ClosedJets Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.ActualReferenceAssembly

/-- GC20's sharp frequency trace at the inner endpoint, by the exact interval reflection. -/
theorem scalar_inner_collar_trace {Value : Type*} [NormedAddCommGroup Value] [InnerProductSpace ℝ Value]
    (curve derivative : ℝ → Value) (lower frequency : ℝ)
    (bounded : lower < 1) (oneLe : 1 ≤ frequency)
    (curveContinuous : Continuous curve) (derivativeContinuous : Continuous derivative)
    (differentiates : ∀ radius ∈ Ioo lower 1, HasDerivAt curve (derivative radius) radius) :
    ‖curve lower‖ ^ 2 ≤ collarTraceConstant lower *
      (frequency * (∫ radius in lower..1, ‖curve radius‖ ^ 2) +
        frequency⁻¹ * (∫ radius in lower..1, ‖derivative radius‖ ^ 2)) := by
  have reflected : ∀ radius ∈ Ioo lower 1,
      HasDerivAt (fun radius => curve (lower + 1 - radius))
        (-derivative (lower + 1 - radius)) radius := by
    intro radius inside
    have inside' : lower + 1 - radius ∈ Ioo lower 1 := ⟨by linarith [inside.2], by linarith [inside.1]⟩
    simpa only [Function.comp_def, neg_smul, one_smul] using
      (differentiates _ inside').scomp radius ((hasDerivAt_id radius).const_sub (lower + 1))
  have estimate := scalar_collar_trace
    (fun radius => curve (lower + 1 - radius)) (fun radius => -derivative (lower + 1 - radius))
    lower frequency bounded oneLe
    (curveContinuous.comp (continuous_const.sub continuous_id))
    ((derivativeContinuous.comp (continuous_const.sub continuous_id)).neg) reflected
  have reflection (function : ℝ → ℝ) :
      (∫ radius in lower..1, function (lower + 1 - radius)) = ∫ radius in lower..1, function radius := by
    simpa only [add_sub_cancel_right, add_sub_cancel_left] using
      intervalIntegral.integral_comp_sub_left function (a := lower) (b := 1) (lower + 1)
  have values := reflection (fun radius => ‖curve radius‖ ^ 2)
  have slopes := reflection (fun radius => ‖derivative radius‖ ^ 2)
  simp only [add_sub_cancel_right, norm_neg] at estimate
  rw [values, slopes] at estimate
  exact estimate

theorem annularFrequency_one_le (mode cell : ℤ) : 1 ≤ annularFrequency mode cell := by
  unfold annularFrequency
  linarith [abs_nonneg (mode : ℝ), abs_nonneg (cell : ℝ)]

def annularPotentialComparison (length : ℝ) : ℝ := 6 + 6 * length ^ 2

theorem annularPotentialComparison_one_le (length : ℝ) : 1 ≤ annularPotentialComparison length := by
  unfold annularPotentialComparison
  nlinarith [sq_nonneg length]

theorem annularFrequency_sq_le_potential (length radius : ℝ) (mode cell : ℤ)
    (lengthPositive : 0 < length) (radiusPositive : 0 < radius) (radiusUpper : radius ≤ 1)
    (high : 3 ≤ |mode|) :
    annularFrequency mode cell ^ 2 ≤ annularPotentialComparison length * annularPotential length radius mode cell := by
  have nine := annularPotential_nine_le length radius mode cell high radiusPositive radiusUpper
  have first : (mode : ℝ) ^ 2 ≤ (mode : ℝ) ^ 2 / radius ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos radiusPositive)).2
    have radiusSq : radius ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg (mode : ℝ)) (sub_nonneg.mpr radiusSq)]
  have second : 0 ≤ highMultiplier mode * (cell : ℝ) ^ 2 / length ^ 2 :=
    div_nonneg (mul_nonneg (highMultiplier_nonnegative _) (sq_nonneg _)) (sq_nonneg _)
  have modePart : (mode : ℝ) ^ 2 ≤ annularPotential length radius mode cell := by
    unfold annularPotential
    linarith
  have multiplier := (highMultiplier_bounds mode (highMode_not_low mode high)).1
  have cellPart : (cell : ℝ) ^ 2 ≤ (9 / 5 : ℝ) * length ^ 2 * annularPotential length radius mode cell := by
    have literal : highMultiplier mode * (cell : ℝ) ^ 2 ≤
        annularPotential length radius mode cell * length ^ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos lengthPositive)).mp
      unfold annularPotential
      exact le_add_of_nonneg_left (div_nonneg (sq_nonneg _) (sq_nonneg _))
    nlinarith [mul_nonneg (sub_nonneg.mpr multiplier) (sq_nonneg (cell : ℝ))]
  have frequency : annularFrequency mode cell ^ 2 ≤ 3 * (1 + (mode : ℝ) ^ 2 + (cell : ℝ) ^ 2) := by
    unfold annularFrequency
    nlinarith [sq_abs (mode : ℝ), sq_abs (cell : ℝ),
      sq_nonneg (|(mode : ℝ)| - 1), sq_nonneg (|(cell : ℝ)| - 1),
      sq_nonneg (|(mode : ℝ)| - |(cell : ℝ)|)]
  unfold annularPotentialComparison
  nlinarith [mul_nonneg (sq_nonneg length) (annularPotential_pos length radius mode cell high radiusPositive).le]

end Grad.AnnularVariational
