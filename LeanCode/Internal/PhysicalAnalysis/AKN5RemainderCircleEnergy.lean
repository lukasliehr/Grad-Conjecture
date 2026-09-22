import AKN4PaidWeightedRemainder

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.ExhaustionSourceAllocation

open Grad.SourceCollarDivision
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace

theorem remainder_finite_angular_paid {dimension grade depth radial angular power : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (paid : depth + angular + radial + power + 2 ≤ grade)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (modes : Finset ℤ) :
    cellFrequency cell ^ (2 * power) *
      (∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * angular) *
        ‖radialCoefficientJet (polarTaylorRemainder depth (phaseWeightedJet parameters cell field)) mode radial radius‖ ^ 2) ≤
      paidRemainderConstant depth (angular + radial) ^ 2 *
        ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2 := by
  let polar := polarTaylorRemainder depth (phaseWeightedJet parameters cell field)
  let jet : ℝ → ComplexEuclidean dimension := fun angle => angularJet angular (radialIter radial polar) (radius, angle)
  have smooth : ContDiff ℝ ∞ polar := polarTaylorRemainder_smooth depth _
  have jetContinuous : Continuous jet :=
    (angularJet_smooth angular _ (radialIter_smooth radial polar smooth)).continuous.comp
      (continuous_const.prodMk continuous_id)
  have bessel := angularJet_bessel_finite angular (radialIter radial polar)
    (radialIter_smooth radial polar smooth)
    (radialIter_periodic radial polar (polarTaylorRemainder_periodic depth _)) radius modes
  have pointBound (angle : ℝ) (inside : angle ∈ Icc (-Real.pi) Real.pi) :
      cellFrequency cell ^ (2 * power) * ‖jet angle‖ ^ 2 ≤
        paidRemainderConstant depth (angular + radial) ^ 2 *
          ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2 := by
    have bound := pow_le_pow_left₀
      (mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _) (norm_nonneg _))
      (polarTaylorRemainder_mixed_paid parameters cell field paid (radius, angle) ⟨⟨nonnegative, bounded⟩, inside⟩) 2
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm power 2] using bound
  have integralBound := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun angle => cellFrequency cell ^ (2 * power) * ‖jet angle‖ ^ 2)
    (g := fun _ => paidRemainderConstant depth (angular + radial) ^ 2 *
      ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2)
    (neg_lt_self Real.pi_pos).le
    ((continuous_const.mul (jetContinuous.norm.pow 2)).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _) pointBound
  rw [intervalIntegral.integral_const] at integralBound
  simp only [smul_eq_mul] at integralBound
  have piNonzero : 2 * Real.pi ≠ 0 := by positivity
  calc
    _ ≤ cellFrequency cell ^ (2 * power) *
        ((2 * Real.pi)⁻¹ * ∫ angle in -Real.pi..Real.pi, ‖jet angle‖ ^ 2) :=
      mul_le_mul_of_nonneg_left bessel (pow_nonneg (cellFrequency_pos cell).le _)
    _ = (2 * Real.pi)⁻¹ *
        (∫ angle in -Real.pi..Real.pi, cellFrequency cell ^ (2 * power) * ‖jet angle‖ ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
      ring
    _ ≤ (2 * Real.pi)⁻¹ * ((Real.pi - -Real.pi) *
        (paidRemainderConstant depth (angular + radial) ^ 2 *
          ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left integralBound (by positivity)
    _ = _ := by field_simp; ring

def remainderAngularBoundConstant (depth power radial : ℕ) : ℝ :=
  (4 : ℝ) ^ (2 * power) *
    (paidRemainderConstant depth radial ^ 2 + paidRemainderConstant depth (power + radial) ^ 2)

theorem remainderAngularBoundConstant_nonnegative (depth power radial : ℕ) : 0 ≤ remainderAngularBoundConstant depth power radial := by
  unfold remainderAngularBoundConstant
  positivity

theorem remainder_finite_frequency_paid {dimension grade depth radial power : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (paid : depth + power + radial + 2 ≤ grade)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (modes : Finset ℤ) :
    (∑ mode ∈ modes, annularFrequency mode cell ^ (2 * power) *
      ‖radialCoefficientJet (polarTaylorRemainder depth (phaseWeightedJet parameters cell field)) mode radial radius‖ ^ 2) ≤
      remainderAngularBoundConstant depth power radial * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2 := by
  let coefficient := fun mode =>
    ‖radialCoefficientJet (polarTaylorRemainder depth (phaseWeightedJet parameters cell field)) mode radial radius‖ ^ 2
  have zeroBound := remainder_finite_angular_paid (angular := 0) (power := power)
    parameters cell field (by omega : depth + 0 + radial + power + 2 ≤ grade) radius nonnegative bounded modes
  have topBound := remainder_finite_angular_paid (angular := power) (power := 0)
    parameters cell field (by omega : depth + power + radial + 0 + 2 ≤ grade) radius nonnegative bounded modes
  simp only [Nat.mul_zero, pow_zero, one_mul, Nat.zero_add] at zeroBound topBound
  calc
    _ ≤ (4 : ℝ) ^ (2 * power) *
        (cellFrequency cell ^ (2 * power) * (∑ mode ∈ modes, coefficient mode) +
          ∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * power) * coefficient mode) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro mode _
      simpa only [mul_add, add_mul, mul_assoc] using mul_le_mul_of_nonneg_right
        (annularFrequency_even_bound mode cell power) (sq_nonneg _)
    _ ≤ (4 : ℝ) ^ (2 * power) *
        (paidRemainderConstant depth radial ^ 2 * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2 +
          paidRemainderConstant depth (power + radial) ^ 2 * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add zeroBound topBound) (by positivity)
    _ = _ := by unfold remainderAngularBoundConstant; ring

end Grad.ExhaustionSourceAllocation
