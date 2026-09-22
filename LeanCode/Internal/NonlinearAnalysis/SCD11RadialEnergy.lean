import SCD10FourierPaidBound

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace

def radialModeEnergy {dimension : ℕ} (lower : ℝ) (power radial : ℕ)
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension) (mode : ℤ) : ℝ :=
  annularFrequency mode cell ^ (2 * power) *
    ∫ radius in lower..1, radius *
      ‖radialCoefficientJet (dividedPolarValue (phaseWeightedJet parameters cell field)) mode radial radius‖ ^ 2

theorem radialModeEnergy_nonnegative {dimension : ℕ} (lower : ℝ)
    (lowerNonnegative : 0 ≤ lower) (lowerBounded : lower ≤ 1) (power radial : ℕ)
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension) (mode : ℤ) :
    0 ≤ radialModeEnergy lower power radial parameters cell field mode := by
  apply mul_nonneg (pow_nonneg (annularFrequency_nonnegative _ _) _)
  apply intervalIntegral.integral_nonneg lowerBounded
  intro radius inside
  exact mul_nonneg (lowerNonnegative.trans inside.1) (sq_nonneg _)

/-- Exact radial L2(r dr) energy, with no conversion to unweighted dr and
no negative power of the annular inner radius. -/
theorem divided_finite_radial_paid {dimension grade radial power : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (paid : power + radial + 3 ≤ grade)
    (lower : ℝ) (lowerNonnegative : 0 ≤ lower) (lowerBounded : lower ≤ 1) (modes : Finset ℤ) :
    (∑ mode ∈ modes, radialModeEnergy lower power radial parameters cell field mode) ≤
      finiteAngularBoundConstant power radial * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2 := by
  let polar := dividedPolarValue (phaseWeightedJet parameters cell field)
  let bound := finiteAngularBoundConstant power radial *
    ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2
  have boundNonnegative : 0 ≤ bound :=
    mul_nonneg (finiteAngularBoundConstant_nonnegative _ _) (sq_nonneg _)
  have coefficientContinuous (mode : ℤ) : Continuous (fun radius =>
      annularFrequency mode cell ^ (2 * power) * (radius * ‖radialCoefficientJet polar mode radial radius‖ ^ 2)) :=
    continuous_const.mul (continuous_id.mul
      ((radialCoefficientJet_smooth polar (dividedPolarValue_smooth _) mode radial).continuous.norm.pow 2))
  have sumContinuous : Continuous (fun radius => ∑ mode ∈ modes,
      annularFrequency mode cell ^ (2 * power) * (radius * ‖radialCoefficientJet polar mode radial radius‖ ^ 2)) :=
    continuous_finsetSum modes (fun mode _ => coefficientContinuous mode)
  have pointBound (radius : ℝ) (inside : radius ∈ Icc lower 1) :
      (∑ mode ∈ modes, annularFrequency mode cell ^ (2 * power) *
        (radius * ‖radialCoefficientJet polar mode radial radius‖ ^ 2)) ≤ bound := by
    have radialNonnegative := lowerNonnegative.trans inside.1
    have frequencyBound := divided_finite_frequency_paid parameters cell field paid radius radialNonnegative inside.2 modes
    calc
      _ = radius * (∑ mode ∈ modes, annularFrequency mode cell ^ (2 * power) *
          ‖radialCoefficientJet polar mode radial radius‖ ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro mode _
        ring
      _ ≤ radius * bound := mul_le_mul_of_nonneg_left frequencyBound radialNonnegative
      _ ≤ bound := mul_le_of_le_one_left boundNonnegative inside.2
  calc
    _ = ∫ radius in lower..1, ∑ mode ∈ modes, annularFrequency mode cell ^ (2 * power) *
        (radius * ‖radialCoefficientJet polar mode radial radius‖ ^ 2) := by
      rw [intervalIntegral.integral_finsetSum (fun mode _ => (coefficientContinuous mode).intervalIntegrable _ _)]
      simp only [intervalIntegral.integral_const_mul, radialModeEnergy, polar]
    _ ≤ ∫ _radius in lower..1, bound :=
      intervalIntegral.integral_mono_on lowerBounded (sumContinuous.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) pointBound
    _ = (1 - lower) * bound := by rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ bound := mul_le_of_le_one_left boundNonnegative (by linarith)

end Grad.SourceCollarDivision
