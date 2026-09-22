import TRM2RowShift

noncomputable section

open scoped BigOperators

namespace Grad.SourceCollarAngular

open Grad.SourceCollarDivision

def annularArrayShiftLinear {dimension radial : ℕ} (lower : ℝ) (power : ℕ) (shift : ℤ) :
    DivisionJetArray dimension lower radial →ₗ[ℂ]
      DivisionJetArray dimension lower radial where
  toFun field := WithLp.toLp 1 (fun index => annularRowShift lower power shift (field index))
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact map_add (annularRowShift lower power shift) (first index) (second index)
  map_smul' scalar field := by
    apply PiLp.ext
    intro index
    exact map_smul (annularRowShift lower power shift) scalar (field index)

@[simp] theorem annularArrayShiftLinear_apply {dimension radial : ℕ} (lower : ℝ)
    (power : ℕ) (shift : ℤ) (field : DivisionJetArray dimension lower radial)
    (index : Fin (radial + 1)) :
    annularArrayShiftLinear lower power shift field index =
      annularRowShift lower power shift (field index) := rfl

theorem annularArrayShiftLinear_norm_le {dimension radial : ℕ} (lower : ℝ)
    (power : ℕ) (shift : ℤ) (field : DivisionJetArray dimension lower radial) :
    ‖annularArrayShiftLinear lower power shift field‖ ≤
      (1 + |(shift : ℝ)|) ^ power * ‖field‖ := by
  rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
  calc
    ∑ index : Fin (radial + 1),
        ‖annularArrayShiftLinear lower power shift field index‖ ≤
      ∑ index : Fin (radial + 1),
        (1 + |(shift : ℝ)|) ^ power * ‖field index‖ :=
      Finset.sum_le_sum (fun index _ => annularRowShiftLinear_norm_le lower power shift (field index))
    _ = (1 + |(shift : ℝ)|) ^ power *
        ∑ index : Fin (radial + 1), ‖field index‖ := by
      rw [Finset.mul_sum]

/-- The angular character multiplier on every weak radial derivative
coordinate.  Its bound is independent of the inner radius and radial order. -/
def annularArrayShift {dimension radial : ℕ} (lower : ℝ) (power : ℕ) (shift : ℤ) :
    DivisionJetArray dimension lower radial →L[ℂ]
      DivisionJetArray dimension lower radial :=
  LinearMap.mkContinuous (annularArrayShiftLinear lower power shift)
    ((1 + |(shift : ℝ)|) ^ power)
    (annularArrayShiftLinear_norm_le lower power shift)

@[simp] theorem annularArrayShift_apply {dimension radial : ℕ} (lower : ℝ)
    (power : ℕ) (shift : ℤ) (field : DivisionJetArray dimension lower radial)
    (index : Fin (radial + 1)) (mode : ℤ × ℤ) :
    annularArrayShift lower power shift field index mode =
      annularShiftScalar power shift mode • field index (mode.1 - shift, mode.2) := rfl

theorem annularArrayShift_norm_le {dimension radial : ℕ} (lower : ℝ)
    (power : ℕ) (shift : ℤ) :
    ‖annularArrayShift (dimension := dimension) (radial := radial) lower power shift‖ ≤
      (1 + |(shift : ℝ)|) ^ power :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

theorem annularArrayUnitShift_norm_le {dimension radial : ℕ} (lower : ℝ)
    (power : ℕ) (shift : ℤ) (unit : |shift| = 1) :
    ‖annularArrayShift (dimension := dimension) (radial := radial) lower power shift‖ ≤
      (2 : ℝ) ^ power := by
  have castUnit : |(shift : ℝ)| = 1 := by
    simpa only [Int.cast_abs, Int.cast_one] using congrArg (fun value : ℤ => (value : ℝ)) unit
  simpa only [castUnit, one_add_one_eq_two] using
    annularArrayShift_norm_le (dimension := dimension) (radial := radial) lower power shift

end Grad.SourceCollarAngular
