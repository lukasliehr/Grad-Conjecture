import AKN5RemainderCircleEnergy
import SCS30PhysicalPolarProjection

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.ExhaustionSourceAllocation

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SourceCollarDivision
open Grad.NonlinearRadial Grad.BoundaryTrace Grad.SourceCollarFullSource

def sourceCircleCoefficient {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) (radius : ℝ) (mode : ℤ) : ComplexEuclidean dimension :=
  angularCoefficient (fun angle => polarTaylorRemainder 0 (phaseWeightedJet parameters cell field) (radius, angle)) mode

theorem sourceCircleCoefficient_literal {dimension : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (mode : ℤ) :
    sourceCircleCoefficient parameters cell field radius mode =
      angularCoefficient (fun angle => cartesianWeight parameters cell (polarPlane (radius, angle)) •
        field.value (polarClosedPoint radius angle nonnegative bounded)) mode := by
  unfold sourceCircleCoefficient
  congr 1
  funext angle
  have literal := polarTaylorRemainder_weighted 0 parameters cell field
    (by intro rank smaller; omega) radius angle nonnegative bounded
  simpa only [pow_zero, one_smul] using literal

theorem sourceCircleCoefficient_remainder {dimension depth : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (flat : VanishingJets depth field) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (mode : ℤ) :
    sourceCircleCoefficient parameters cell field radius mode =
      radius ^ depth • radialCoefficientJet
        (polarTaylorRemainder depth (phaseWeightedJet parameters cell field)) mode 0 radius := by
  rw [sourceCircleCoefficient_literal parameters cell field radius nonnegative bounded]
  have expression : (fun angle => cartesianWeight parameters cell (polarPlane (radius, angle)) •
      field.value (polarClosedPoint radius angle nonnegative bounded)) =
        fun angle => radius ^ depth • polarTaylorRemainder depth (phaseWeightedJet parameters cell field) (radius, angle) := by
    funext angle
    exact (polarTaylorRemainder_weighted depth parameters cell field flat radius angle nonnegative bounded).symm
  rw [expression, angularCoefficient_real_smul]
  rfl

/-- Exact original-width circle decay. `depth = 3` pays `power + 5`,
and `depth = 2` pays `power + 4`; every angular mode is retained. -/
theorem finite_sourceCircle_decay {dimension grade depth power : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (flat : VanishingJets depth field) (paid : depth + power + 2 ≤ grade)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (modes : Finset ℤ) :
    (∑ mode ∈ modes, annularFrequency mode cell ^ (2 * power) *
      ‖sourceCircleCoefficient parameters cell field radius mode‖ ^ 2) ≤
      radius ^ (2 * depth) * (remainderAngularBoundConstant depth power 0 *
        ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2) := by
  have coefficient (mode : ℤ) : ‖sourceCircleCoefficient parameters cell field radius mode‖ ^ 2 =
      radius ^ (2 * depth) * ‖radialCoefficientJet
        (polarTaylorRemainder depth (phaseWeightedJet parameters cell field)) mode 0 radius‖ ^ 2 := by
    rw [sourceCircleCoefficient_remainder parameters cell field flat radius nonnegative bounded,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg nonnegative _), mul_pow, ← pow_mul]
    rw [Nat.mul_comm depth 2]
  simp_rw [coefficient]
  have bound := remainder_finite_frequency_paid (depth := depth) (radial := 0) (power := power)
    parameters cell field (by omega) radius nonnegative bounded modes
  calc
    _ = radius ^ (2 * depth) * (∑ mode ∈ modes, annularFrequency mode cell ^ (2 * power) *
        ‖radialCoefficientJet (polarTaylorRemainder depth (phaseWeightedJet parameters cell field)) mode 0 radius‖ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mode _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left bound (pow_nonneg nonnegative _)

end Grad.ExhaustionSourceAllocation
