import AKDT27SignedStabilizerUpper

noncomputable section
open Set

namespace Grad.PhysicalGeometry
open Grad.MainTarget

theorem rotation_add_integral_period (angle : ℝ) (integer : ℤ) (point : Vec) :
    rotation (angle + integer * (2 * Real.pi)) point = rotation angle point := by
  ext coordinate
  fin_cases coordinate <;> simp [rotation, vector, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- Euclidean division gives the exact finite rotation index of the unchanged
target, even when the harmonic integer is negative. -/
theorem integral_rotation_finite_index (period : ℕ) (positive : 0 < period) (integer : ℤ) :
    ∃ index : ℕ, index < period ∧ ∀ point : Vec,
      rotation (2 * Real.pi * integer / period) point = rotation (2 * Real.pi * index / period) point := by
  let remainder : ℤ := integer % (period : ℤ)
  have periodIntPositive : (0 : ℤ) < period := Nat.cast_pos.mpr positive
  have nonnegative : 0 ≤ remainder := Int.emod_nonneg integer (ne_of_gt periodIntPositive)
  have bounded : remainder < period := Int.emod_lt_of_pos integer periodIntPositive
  let index : ℕ := remainder.toNat
  have indexCast : (index : ℤ) = remainder := Int.toNat_of_nonneg nonnegative
  have indexBound : index < period := by
    have castBound : (index : ℤ) < period := indexCast ▸ bounded
    exact_mod_cast castBound
  have decomposition : (integer : ℝ) = (index : ℝ) + (period : ℝ) * ((integer / (period : ℤ) : ℤ) : ℝ) := by
    have original := Int.emod_add_mul_ediv integer (period : ℤ)
    change remainder + (period : ℤ) * (integer / (period : ℤ)) = integer at original
    rw [← indexCast] at original
    exact_mod_cast original.symm
  have periodNonzero : (period : ℝ) ≠ 0 := (Nat.cast_pos.mpr positive).ne'
  have angleSame : 2 * Real.pi * integer / period =
      2 * Real.pi * index / period + ((integer / (period : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [decomposition]
    field_simp
  refine ⟨index, indexBound, ?_⟩
  intro point
  rw [angleSame, rotation_add_integral_period]

end Grad.PhysicalGeometry
