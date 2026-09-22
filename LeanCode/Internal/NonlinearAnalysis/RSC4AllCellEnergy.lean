import RSC3AnnularBessel
import BT18Summation

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.SourceCollarRestriction

open Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace

def originalRestrictionEnergy {dimension : ℕ} (lower : ℝ) (power radial : ℕ)
    (parameters : PhaseParameters) (field : ACore parameters dimension) (mode : ℤ × ℤ) : ℝ :=
  restrictionModeEnergy lower power radial parameters mode.2 (field.val mode.2) mode.1

theorem originalRestrictionEnergy_nonnegative {dimension : ℕ} (lower : ℝ)
    (lowerNonnegative : 0 ≤ lower) (lowerBounded : lower ≤ 1) (power radial : ℕ)
    (parameters : PhaseParameters) (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    0 ≤ originalRestrictionEnergy lower power radial parameters field mode :=
  restrictionModeEnergy_nonnegative lower lowerNonnegative lowerBounded power radial parameters mode.2 (field.val mode.2) mode.1

theorem finite_original_restriction_bound {dimension grade radial power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (paid : power + radial ≤ grade)
    (lower : ℝ) (lowerNonnegative : 0 ≤ lower) (lowerBounded : lower ≤ 1) (modes : Finset (ℤ × ℤ)) :
    (∑ mode ∈ modes, originalRestrictionEnergy lower power radial parameters field mode) ≤
      restrictionRowConstant power radial * ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 := by
  classical
  have rectangular : modes ⊆ modes.image Prod.fst ×ˢ modes.image Prod.snd := by
    intro mode member
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨mode, member, rfl⟩,
      Finset.mem_image.mpr ⟨mode, member, rfl⟩⟩
  calc
    _ ≤ ∑ mode ∈ modes.image Prod.fst ×ˢ modes.image Prod.snd,
        originalRestrictionEnergy lower power radial parameters field mode :=
      Finset.sum_le_sum_of_subset_of_nonneg rectangular
        (fun mode _ _ => originalRestrictionEnergy_nonnegative lower lowerNonnegative lowerBounded power radial parameters field mode)
    _ = ∑ cell ∈ modes.image Prod.snd, ∑ mode ∈ modes.image Prod.fst,
        restrictionModeEnergy lower power radial parameters cell (field.val cell) mode := by
      rw [Finset.sum_product, Finset.sum_comm]
      rfl
    _ ≤ ∑ cell ∈ modes.image Prod.snd,
        restrictionRowConstant power radial * ‖cellGradeRowLinear (grade := grade) parameters cell (field.val cell)‖ ^ 2 :=
      Finset.sum_le_sum (fun cell _ => restriction_finite_radial_paid parameters cell (field.val cell) paid
        lower lowerNonnegative lowerBounded _)
    _ = restrictionRowConstant power radial * (∑ cell ∈ modes.image Prod.snd,
        ‖cellGradeRowLinear (grade := grade) parameters cell (field.val cell)‖ ^ 2) := by rw [Finset.mul_sum]
    _ ≤ restrictionRowConstant power radial * (∑' cell : ℤ,
        ‖cellGradeRowLinear (grade := grade) parameters cell (field.val cell)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        ((original_rows_summable parameters field).sum_le_tsum _ (fun _ _ => sq_nonneg _))
        (restrictionRowConstant_nonnegative _ _)
    _ = _ := by rw [originalGrade_norm_sq_eq_rows]

theorem original_restriction_summable {dimension grade radial power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (paid : power + radial ≤ grade)
    (lower : ℝ) (lowerNonnegative : 0 ≤ lower) (lowerBounded : lower ≤ 1) :
    Summable (originalRestrictionEnergy lower power radial parameters field) :=
  summable_of_sum_le (originalRestrictionEnergy_nonnegative lower lowerNonnegative lowerBounded power radial parameters field)
    (finite_original_restriction_bound parameters field paid lower lowerNonnegative lowerBounded)

theorem original_restriction_energy_bound {dimension grade radial power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (paid : power + radial ≤ grade)
    (lower : ℝ) (lowerNonnegative : 0 ≤ lower) (lowerBounded : lower ≤ 1) :
    (∑' mode : ℤ × ℤ, originalRestrictionEnergy lower power radial parameters field mode) ≤
      restrictionRowConstant power radial * ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 :=
  Real.tsum_le_of_sum_le (originalRestrictionEnergy_nonnegative lower lowerNonnegative lowerBounded power radial parameters field)
    (finite_original_restriction_bound parameters field paid lower lowerNonnegative lowerBounded)

/-- BS34 is a sum of the radial derivative L2 norms, not their Hilbert sum. -/
def originalRestrictionGraphNorm {dimension : ℕ} (lower : ℝ) (power radial : ℕ)
    (parameters : PhaseParameters) (field : ACore parameters dimension) : ℝ :=
  ∑ index ∈ Finset.range (radial + 1),
    Real.sqrt (∑' mode : ℤ × ℤ, originalRestrictionEnergy lower power index parameters field mode)

def restrictionGraphConstant (power radial : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (radial + 1), Real.sqrt (restrictionRowConstant power index)

theorem restrictionGraphConstant_nonnegative (power radial : ℕ) : 0 ≤ restrictionGraphConstant power radial :=
  Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)

theorem original_restriction_graph_bound {dimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension) (power radial : ℕ)
    (lower : ℝ) (lowerNonnegative : 0 ≤ lower) (lowerBounded : lower ≤ 1) :
    originalRestrictionGraphNorm lower power radial parameters field ≤
      restrictionGraphConstant power radial * ‖GradeCore.ofCoreLinear (grade := power + radial) field‖ := by
  rw [originalRestrictionGraphNorm, restrictionGraphConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index inside
  have bound := Finset.mem_range.mp inside
  apply (Real.sqrt_le_sqrt (original_restriction_energy_bound parameters field
    (by omega : power + index ≤ power + radial) lower lowerNonnegative lowerBounded)).trans_eq
  rw [Real.sqrt_mul (restrictionRowConstant_nonnegative _ _), Real.sqrt_sq (norm_nonneg _)]

end Grad.SourceCollarRestriction
