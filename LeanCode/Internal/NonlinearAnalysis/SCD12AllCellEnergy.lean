import SCD11RadialEnergy
import BT18Summation

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace

def originalDivisionEnergy {dimension : ℕ} (lower : ℝ) (power radial : ℕ)
    (parameters : PhaseParameters) (field : ACore parameters dimension) (mode : ℤ × ℤ) : ℝ :=
  radialModeEnergy lower power radial parameters mode.2 (field.val mode.2) mode.1

theorem originalDivisionEnergy_nonnegative {dimension : ℕ} (lower : ℝ)
    (lowerNonnegative : 0 ≤ lower) (lowerBounded : lower ≤ 1) (power radial : ℕ)
    (parameters : PhaseParameters) (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    0 ≤ originalDivisionEnergy lower power radial parameters field mode :=
  radialModeEnergy_nonnegative lower lowerNonnegative lowerBounded power radial parameters mode.2 (field.val mode.2) mode.1

theorem finite_original_division_bound {dimension grade radial power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (paid : power + radial + 3 ≤ grade)
    (lower : ℝ) (lowerNonnegative : 0 ≤ lower) (lowerBounded : lower ≤ 1) (modes : Finset (ℤ × ℤ)) :
    (∑ mode ∈ modes, originalDivisionEnergy lower power radial parameters field mode) ≤
      finiteAngularBoundConstant power radial * ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 := by
  classical
  have rectangular : modes ⊆ modes.image Prod.fst ×ˢ modes.image Prod.snd := by
    intro mode member
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨mode, member, rfl⟩,
      Finset.mem_image.mpr ⟨mode, member, rfl⟩⟩
  calc
    _ ≤ ∑ mode ∈ modes.image Prod.fst ×ˢ modes.image Prod.snd,
        originalDivisionEnergy lower power radial parameters field mode :=
      Finset.sum_le_sum_of_subset_of_nonneg rectangular
        (fun mode _ _ => originalDivisionEnergy_nonnegative lower lowerNonnegative lowerBounded power radial parameters field mode)
    _ = ∑ cell ∈ modes.image Prod.snd, ∑ mode ∈ modes.image Prod.fst,
        radialModeEnergy lower power radial parameters cell (field.val cell) mode := by
      rw [Finset.sum_product, Finset.sum_comm]
      rfl
    _ ≤ ∑ cell ∈ modes.image Prod.snd,
        finiteAngularBoundConstant power radial * ‖cellGradeRowLinear (grade := grade) parameters cell (field.val cell)‖ ^ 2 :=
      Finset.sum_le_sum (fun cell _ => divided_finite_radial_paid parameters cell (field.val cell) paid
        lower lowerNonnegative lowerBounded _)
    _ = finiteAngularBoundConstant power radial * (∑ cell ∈ modes.image Prod.snd,
        ‖cellGradeRowLinear (grade := grade) parameters cell (field.val cell)‖ ^ 2) := by rw [Finset.mul_sum]
    _ ≤ finiteAngularBoundConstant power radial * (∑' cell : ℤ,
        ‖cellGradeRowLinear (grade := grade) parameters cell (field.val cell)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        ((original_rows_summable parameters field).sum_le_tsum _ (fun _ _ => sq_nonneg _))
        (finiteAngularBoundConstant_nonnegative _ _)
    _ = _ := by rw [originalGrade_norm_sq_eq_rows]

theorem original_division_summable {dimension grade radial power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (paid : power + radial + 3 ≤ grade)
    (lower : ℝ) (lowerNonnegative : 0 ≤ lower) (lowerBounded : lower ≤ 1) :
    Summable (originalDivisionEnergy lower power radial parameters field) :=
  summable_of_sum_le (originalDivisionEnergy_nonnegative lower lowerNonnegative lowerBounded power radial parameters field)
    (finite_original_division_bound parameters field paid lower lowerNonnegative lowerBounded)

theorem original_division_energy_bound {dimension grade radial power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (paid : power + radial + 3 ≤ grade)
    (lower : ℝ) (lowerNonnegative : 0 ≤ lower) (lowerBounded : lower ≤ 1) :
    (∑' mode : ℤ × ℤ, originalDivisionEnergy lower power radial parameters field mode) ≤
      finiteAngularBoundConstant power radial * ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 :=
  Real.tsum_le_of_sum_le (originalDivisionEnergy_nonnegative lower lowerNonnegative lowerBounded power radial parameters field)
    (finite_original_division_bound parameters field paid lower lowerNonnegative lowerBounded)

/-- BS34 is a sum of the radial derivative L2 norms, not their Hilbert sum. -/
def originalDivisionGraphNorm {dimension : ℕ} (lower : ℝ) (power radial : ℕ)
    (parameters : PhaseParameters) (field : ACore parameters dimension) : ℝ :=
  ∑ index ∈ Finset.range (radial + 1),
    Real.sqrt (∑' mode : ℤ × ℤ, originalDivisionEnergy lower power index parameters field mode)

def divisionGraphConstant (power radial : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (radial + 1), Real.sqrt (finiteAngularBoundConstant power index)

theorem divisionGraphConstant_nonnegative (power radial : ℕ) : 0 ≤ divisionGraphConstant power radial :=
  Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)

theorem original_division_graph_bound {dimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension) (power radial : ℕ)
    (lower : ℝ) (lowerNonnegative : 0 ≤ lower) (lowerBounded : lower ≤ 1) :
    originalDivisionGraphNorm lower power radial parameters field ≤
      divisionGraphConstant power radial * ‖GradeCore.ofCoreLinear (grade := power + radial + 3) field‖ := by
  rw [originalDivisionGraphNorm, divisionGraphConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index inside
  have bound := Finset.mem_range.mp inside
  apply (Real.sqrt_le_sqrt (original_division_energy_bound parameters field
    (by omega : power + index + 3 ≤ power + radial + 3) lower lowerNonnegative lowerBounded)).trans_eq
  rw [Real.sqrt_mul (finiteAngularBoundConstant_nonnegative _ _), Real.sqrt_sq (norm_nonneg _)]

end Grad.SourceCollarDivision
