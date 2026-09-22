import TRM3JetShift

noncomputable section

namespace Grad.SourceCollarAngular

open Grad.SourceCollarDivision

theorem annularArrayShift_mem_graph {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (power : ℕ) (shift : ℤ)
    (field : annularDerivativeGraph dimension lower positive radial) :
    annularArrayShift lower power shift field.val ∈
      annularDerivativeGraph dimension lower positive radial := by
  apply (annularDerivativeGraph_mem_iff lower positive radial _).mpr
  intro index mode
  change HasWeakRadialDerivative lower positive
    (annularShiftScalar power shift mode •
      field.val index.castSucc (mode.1 - shift, mode.2))
    (annularShiftScalar power shift mode •
      field.val index.succ (mode.1 - shift, mode.2))
  exact ((annularDerivativeGraph_mem_iff lower positive radial field.val).mp field.property
    index (mode.1 - shift, mode.2)).smul _

/-- Multiplication by one angular character on the complete weak radial
graph.  It preserves all weak radial derivative coordinates exactly. -/
def annularGraphShift {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (power : ℕ) (shift : ℤ) :
    annularDerivativeGraph dimension lower positive radial →L[ℂ]
      annularDerivativeGraph dimension lower positive radial :=
  ((annularArrayShift lower power shift).comp
    (annularDerivativeGraph dimension lower positive radial).subtypeL).codRestrict
      (annularDerivativeGraph dimension lower positive radial)
      (annularArrayShift_mem_graph lower positive power shift)

@[simp] theorem annularGraphShift_apply {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (power : ℕ) (shift : ℤ)
    (field : annularDerivativeGraph dimension lower positive radial)
    (index : Fin (radial + 1)) (mode : ℤ × ℤ) :
    (annularGraphShift lower positive power shift field).val index mode =
      annularShiftScalar power shift mode •
        field.val index (mode.1 - shift, mode.2) := rfl

theorem annularGraphShift_apply_norm_le {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (power : ℕ) (shift : ℤ)
    (field : annularDerivativeGraph dimension lower positive radial) :
    ‖annularGraphShift lower positive power shift field‖ ≤
      (1 + |(shift : ℝ)|) ^ power * ‖field‖ := by
  exact annularArrayShiftLinear_norm_le lower power shift field.val

theorem annularGraphShift_norm_le {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (power : ℕ) (shift : ℤ) :
    ‖annularGraphShift (dimension := dimension) (radial := radial)
      lower positive power shift‖ ≤ (1 + |(shift : ℝ)|) ^ power := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact annularGraphShift_apply_norm_le lower positive power shift

theorem annularGraphUnitShift_norm_le {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (power : ℕ) (shift : ℤ)
    (unit : |shift| = 1) :
    ‖annularGraphShift (dimension := dimension) (radial := radial)
      lower positive power shift‖ ≤ (2 : ℝ) ^ power := by
  have castUnit : |(shift : ℝ)| = 1 := by
    simpa only [Int.cast_abs, Int.cast_one] using congrArg (fun value : ℤ => (value : ℝ)) unit
  simpa only [castUnit, one_add_one_eq_two] using
    annularGraphShift_norm_le (dimension := dimension) (radial := radial)
      lower positive power shift

end Grad.SourceCollarAngular
