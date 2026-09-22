import GC8Interface

noncomputable section

open Grad.PDEBootstrap Grad.AnalyticWeights.Calculus

namespace Grad.GaugeCoefficients.Envelope

theorem admissible_gamma_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) : 0 ≤ gamma := admissible.2.1.le

theorem admissible_ell_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) : 0 ≤ ell := admissible.2.2.2.1.le

theorem admissible_gamma_le_sigma {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) : gamma ≤ sigma :=
  ((lt_min_iff.mp admissible.2.2.1).2).le

theorem admissible_ell_le_one {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) : ell ≤ 1 :=
  admissible.2.2.2.2.trans (min_le_left 1 L)

theorem admissible_ell_le_L {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) : ell ≤ L :=
  admissible.2.2.2.2.trans (min_le_right 1 L)

theorem norm_le_one_of_mem_closedDisk {point : Spatial} (membership : point ∈ closedDisk) :
    ‖point‖ ≤ 1 := by
  simpa only [closedDisk, Metric.mem_closedBall, dist_zero_right] using membership

theorem admissible_scaled_radius_le_one {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {point : Spatial}
    (membership : point ∈ closedDisk) : ell * ‖point‖ ≤ 1 := by
  calc
    ell * ‖point‖ ≤ 1 * ‖point‖ :=
      mul_le_mul_of_nonneg_right (admissible_ell_le_one admissible) (norm_nonneg point)
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left (norm_le_one_of_mem_closedDisk membership) zero_le_one
    _ = 1 := one_mul 1

theorem admissible_rate_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {point : Spatial}
    (membership : point ∈ closedDisk) :
    0 ≤ Grad.AnalyticWeights.rate sigma gamma (ell * ‖point‖) := by
  have productBound := mul_le_mul_of_nonneg_left
    (admissible_scaled_radius_le_one admissible membership)
    (admissible_gamma_nonnegative admissible)
  unfold Grad.AnalyticWeights.rate
  linarith [admissible_gamma_le_sigma admissible]

theorem envelopeGoal : EnvelopeGoal := by
  intro L sigma gamma ell admissible cell point membership
  have gammaNonnegative := admissible_gamma_nonnegative admissible
  have ellNonnegative := admissible_ell_nonnegative admissible
  have radiusNonnegative : 0 ≤ ell * ‖point‖ := mul_nonneg ellNonnegative (norm_nonneg point)
  have rateNonnegative := admissible_rate_nonnegative admissible membership
  have bounds := Grad.AnalyticWeights.weight_absolute_bounds sigma gamma (ell * ‖point‖) cell
    gammaNonnegative radiusNonnegative rateNonnegative
  have rateExpression : 0 ≤ sigma - gamma * ell * ‖point‖ := by
    simpa only [Grad.AnalyticWeights.rate, mul_assoc] using rateNonnegative
  refine ⟨Real.one_le_exp (mul_nonneg rateExpression (abs_nonneg _)), ?_, ?_⟩
  · simpa only [originalEnvelope, originalWeight, physicalWeight, Grad.AnalyticWeights.rate,
      mul_assoc] using bounds.1
  · simpa only [originalEnvelope, originalWeight, phaseConstant, physicalWeight,
      Grad.AnalyticWeights.rate, mul_assoc] using bounds.2

theorem ratioGoal : RatioGoal := by
  intro L sigma gamma ell admissible base displacement point membership
  have estimate := Grad.AnalyticWeights.physical_weight_ratio sigma gamma ell
    (base + displacement) base point (admissible_gamma_nonnegative admissible)
      (admissible_ell_nonnegative admissible) (admissible_rate_nonnegative admissible membership)
  simpa [originalWeight, physicalWeight, phaseConstant, originalEnvelope,
    Grad.AnalyticWeights.envelope, Grad.RepresentedKernel.radialEnvelope,
    Grad.AnalyticWeights.rate, mul_assoc] using estimate

end Grad.GaugeCoefficients.Envelope
