import AKN6ActualWeightedCircleDecay
import SCD12AllCellEnergy

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.ExhaustionSourceAllocation

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SourceCollarDivision
open Grad.NonlinearRadial Grad.BoundaryTrace

def sourceCircleEnergy {dimension : ℕ} (parameters : PhaseParameters)
    (power : ℕ) (field : ACore parameters dimension) (radius : ℝ) (mode : ℤ × ℤ) : ℝ :=
  annularFrequency mode.1 mode.2 ^ (2 * power) *
    ‖sourceCircleCoefficient parameters mode.2 (field.val mode.2) radius mode.1‖ ^ 2

theorem sourceCircleEnergy_nonnegative {dimension : ℕ} (parameters : PhaseParameters)
    (power : ℕ) (field : ACore parameters dimension) (radius : ℝ) (mode : ℤ × ℤ) :
    0 ≤ sourceCircleEnergy parameters power field radius mode :=
  mul_nonneg (pow_nonneg (annularFrequency_nonnegative _ _) _) (sq_nonneg _)

theorem finite_fullCircle_decay {dimension grade depth power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (flat : ∀ cell, VanishingJets depth (field.val cell)) (paid : depth + power + 2 ≤ grade)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (modes : Finset (ℤ × ℤ)) :
    (∑ mode ∈ modes, sourceCircleEnergy parameters power field radius mode) ≤
      radius ^ (2 * depth) * remainderAngularBoundConstant depth power 0 *
        ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 := by
  classical
  have constantNonnegative : 0 ≤ radius ^ (2 * depth) * remainderAngularBoundConstant depth power 0 :=
    mul_nonneg (pow_nonneg nonnegative _) (remainderAngularBoundConstant_nonnegative _ _ _)
  have rectangular : modes ⊆ modes.image Prod.fst ×ˢ modes.image Prod.snd := by
    intro mode member
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨mode, member, rfl⟩,
      Finset.mem_image.mpr ⟨mode, member, rfl⟩⟩
  calc
    _ ≤ ∑ mode ∈ modes.image Prod.fst ×ˢ modes.image Prod.snd,
        sourceCircleEnergy parameters power field radius mode :=
      Finset.sum_le_sum_of_subset_of_nonneg rectangular
        (fun mode _ _ => sourceCircleEnergy_nonnegative parameters power field radius mode)
    _ = ∑ cell ∈ modes.image Prod.snd, ∑ mode ∈ modes.image Prod.fst,
        annularFrequency mode cell ^ (2 * power) *
          ‖sourceCircleCoefficient parameters cell (field.val cell) radius mode‖ ^ 2 := by
      rw [Finset.sum_product, Finset.sum_comm]
      rfl
    _ ≤ ∑ cell ∈ modes.image Prod.snd, radius ^ (2 * depth) *
        (remainderAngularBoundConstant depth power 0 *
          ‖cellGradeRowLinear (grade := grade) parameters cell (field.val cell)‖ ^ 2) :=
      Finset.sum_le_sum (fun cell _ => finite_sourceCircle_decay parameters cell (field.val cell)
        (flat cell) paid radius nonnegative bounded _)
    _ = (radius ^ (2 * depth) * remainderAngularBoundConstant depth power 0) *
        (∑ cell ∈ modes.image Prod.snd, ‖cellGradeRowLinear (grade := grade) parameters cell (field.val cell)‖ ^ 2) := by
      simp only [mul_assoc, Finset.mul_sum]
    _ ≤ (radius ^ (2 * depth) * remainderAngularBoundConstant depth power 0) *
        (∑' cell : ℤ, ‖cellGradeRowLinear (grade := grade) parameters cell (field.val cell)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        ((original_rows_summable parameters field).sum_le_tsum _ (fun _ _ => sq_nonneg _)) constantNonnegative
    _ = _ := by rw [originalGrade_norm_sq_eq_rows]

/-- The full angular and axial Hilbert circle estimate before any radial
integration. It retains every mode and the unchanged Cartesian phase. -/
theorem fullCircle_decay {dimension grade depth power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (flat : ∀ cell, VanishingJets depth (field.val cell)) (paid : depth + power + 2 ≤ grade)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    (∑' mode : ℤ × ℤ, sourceCircleEnergy parameters power field radius mode) ≤
      radius ^ (2 * depth) * remainderAngularBoundConstant depth power 0 *
        ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 :=
  Real.tsum_le_of_sum_le (sourceCircleEnergy_nonnegative parameters power field radius)
    (finite_fullCircle_decay parameters field flat paid radius nonnegative bounded)

theorem fullCircle_summable {dimension grade depth power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (flat : ∀ cell, VanishingJets depth (field.val cell)) (paid : depth + power + 2 ≤ grade)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (sourceCircleEnergy parameters power field radius) :=
  summable_of_sum_le (sourceCircleEnergy_nonnegative parameters power field radius)
    (finite_fullCircle_decay parameters field flat paid radius nonnegative bounded)

end Grad.ExhaustionSourceAllocation
