import RSC2AnnularIntegral

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.SourceCollarRestriction

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.BoundaryTrace
open Grad.SourceCollarDivision

def annularCoefficientEnergy {dimension : ℕ} (lower : ℝ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (mode : ℤ) : ℝ :=
  ∫ radius in lower..1, radius * ‖angularCoefficient (fun angle => field (radius, angle)) mode‖ ^ 2

theorem annularCoefficientEnergy_nonnegative {dimension : ℕ} (lower : ℝ)
    (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (mode : ℤ) :
    0 ≤ annularCoefficientEnergy lower field mode :=
  intervalIntegral.integral_nonneg bounded
    (fun _ inside => mul_nonneg (nonnegative.trans inside.1) (sq_nonneg _))

theorem annular_angular_bessel {dimension : ℕ} (lower : ℝ)
    (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1) (order : ℕ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (periodic : Function.Periodic field (0, 2 * Real.pi)) (modes : Finset ℤ) :
    (∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * order) * annularCoefficientEnergy lower field mode) ≤
      (2 * Real.pi)⁻¹ * annularIntegral lower (fun point => ‖angularJet order field point‖ ^ 2) := by
  have coefficientContinuous (mode : ℤ) : Continuous (fun radius =>
      |(mode : ℝ)| ^ (2 * order) * (radius * ‖angularCoefficient (fun angle => field (radius, angle)) mode‖ ^ 2)) :=
    continuous_const.mul (continuous_id.mul ((angularCoefficient_smooth field smooth mode).continuous.norm.pow 2))
  have jetContinuous : Continuous (fun point => ‖angularJet order field point‖ ^ 2) :=
    (angularJet_smooth order field smooth).continuous.norm.pow 2
  have angularContinuous : Continuous (fun radius =>
      ∫ angle in -Real.pi..Real.pi, ‖angularJet order field (radius, angle)‖ ^ 2) :=
    timeIntegral_continuous _ (jetContinuous.comp continuous_swap) (-Real.pi) Real.pi (neg_lt_self Real.pi_pos).le
  have comparison := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun radius => ∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * order) *
      (radius * ‖angularCoefficient (fun angle => field (radius, angle)) mode‖ ^ 2))
    (g := fun radius => (2 * Real.pi)⁻¹ * (radius * ∫ angle in -Real.pi..Real.pi,
      ‖angularJet order field (radius, angle)‖ ^ 2)) bounded
    ((continuous_finsetSum modes (fun mode _ => coefficientContinuous mode)).intervalIntegrable _ _)
    ((continuous_const.mul (continuous_id.mul angularContinuous)).intervalIntegrable _ _)
    (fun radius inside => by
      have bessel := mul_le_mul_of_nonneg_left (angularJet_bessel_finite order field smooth periodic radius modes)
        (nonnegative.trans inside.1)
      simpa only [Finset.mul_sum, mul_left_comm radius] using bessel)
  rw [intervalIntegral.integral_finsetSum (fun mode _ => (coefficientContinuous mode).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, annularIntegral_swap lower bounded _ jetContinuous] at comparison
  simpa only [intervalIntegral.integral_const_mul, annularCoefficientEnergy] using comparison

theorem original_annular_bessel_paid {dimension grade radial angular power : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (paid : angular + radial + power ≤ grade)
    (lower : ℝ) (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1) (modes : Finset ℤ) :
    cellFrequency cell ^ (2 * power) * (∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * angular) *
      annularCoefficientEnergy lower (radialIter radial (originalPolarValue (phaseWeightedJet parameters cell field))) mode) ≤
      ((2 * Real.pi)⁻¹ * polarOrderConstant (angular + radial)) *
        ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2 := by
  let polar := originalPolarValue (phaseWeightedJet parameters cell field)
  have bessel := annular_angular_bessel lower nonnegative bounded angular (radialIter radial polar)
    (radialIter_smooth radial polar (originalPolarValue_smooth _))
    (radialIter_periodic radial polar (originalPolarValue_periodic _)) modes
  have bound := original_polar_mixed_integral_bound parameters cell field paid lower nonnegative bounded
  calc
    _ ≤ cellFrequency cell ^ (2 * power) * ((2 * Real.pi)⁻¹ *
        annularIntegral lower (fun point => ‖angularJet angular (radialIter radial polar) point‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left bessel (pow_nonneg (cellFrequency_pos cell).le _)
    _ = (2 * Real.pi)⁻¹ * (cellFrequency cell ^ (2 * power) *
        annularIntegral lower (fun point => ‖angularJet angular (radialIter radial polar) point‖ ^ 2)) := by ring
    _ ≤ (2 * Real.pi)⁻¹ * (polarOrderConstant (angular + radial) *
        ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2) :=
      mul_le_mul_of_nonneg_left bound (by positivity)
    _ = _ := by ring

def restrictionModeEnergy {dimension : ℕ} (lower : ℝ) (power radial : ℕ)
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension) (mode : ℤ) : ℝ :=
  annularFrequency mode cell ^ (2 * power) *
    annularCoefficientEnergy lower (radialIter radial (originalPolarValue (phaseWeightedJet parameters cell field))) mode

theorem restrictionModeEnergy_nonnegative {dimension : ℕ} (lower : ℝ)
    (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1) (power radial : ℕ)
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension) (mode : ℤ) :
    0 ≤ restrictionModeEnergy lower power radial parameters cell field mode :=
  mul_nonneg (pow_nonneg (annularFrequency_nonnegative _ _) _)
    (annularCoefficientEnergy_nonnegative lower nonnegative bounded _ _)

def restrictionRowConstant (power radial : ℕ) : ℝ :=
  (4 : ℝ) ^ (2 * power) * (2 * Real.pi)⁻¹ *
    (polarOrderConstant radial + polarOrderConstant (power + radial))

theorem restrictionRowConstant_nonnegative (power radial : ℕ) : 0 ≤ restrictionRowConstant power radial := by
  unfold restrictionRowConstant
  exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (add_nonneg (polarOrderConstant_nonnegative _) (polarOrderConstant_nonnegative _))

theorem restriction_finite_radial_paid {dimension grade radial power : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (paid : power + radial ≤ grade)
    (lower : ℝ) (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1) (modes : Finset ℤ) :
    (∑ mode ∈ modes, restrictionModeEnergy lower power radial parameters cell field mode) ≤
      restrictionRowConstant power radial * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2 := by
  let energy := annularCoefficientEnergy lower
    (radialIter radial (originalPolarValue (phaseWeightedJet parameters cell field)))
  have zeroBound := original_annular_bessel_paid (angular := 0) (power := power)
    parameters cell field (by omega : 0 + radial + power ≤ grade) lower nonnegative bounded modes
  have topBound := original_annular_bessel_paid (angular := power) (power := 0)
    parameters cell field (by omega : power + radial + 0 ≤ grade) lower nonnegative bounded modes
  simp only [Nat.mul_zero, pow_zero, one_mul, Nat.zero_add] at zeroBound topBound
  calc
    _ ≤ (4 : ℝ) ^ (2 * power) * (cellFrequency cell ^ (2 * power) * (∑ mode ∈ modes, energy mode) +
        ∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * power) * energy mode) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro mode _
      simpa only [restrictionModeEnergy, energy, mul_add, add_mul, mul_assoc] using
        mul_le_mul_of_nonneg_right (annularFrequency_even_bound mode cell power)
          (annularCoefficientEnergy_nonnegative lower nonnegative bounded _ _)
    _ ≤ (4 : ℝ) ^ (2 * power) *
        (((2 * Real.pi)⁻¹ * polarOrderConstant radial) * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2 +
          ((2 * Real.pi)⁻¹ * polarOrderConstant (power + radial)) *
            ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add zeroBound topBound) (by positivity)
    _ = _ := by unfold restrictionRowConstant; ring

end Grad.SourceCollarRestriction
