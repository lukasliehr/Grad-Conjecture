import SCS9LiteralPrimitiveRows

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.BoundaryTrace Grad.SourceCollarCoefficients Grad.PhaseAlgebra

theorem cartesianWeight_polar (parameters : PhaseParameters) (cell : ℤ)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) :
    cartesianWeight parameters cell (polarPlane (radius, angle)) =
      Real.exp (radialPhase parameters radius cell) := by
  rw [cartesianWeight_exp, radialPhase_eq_cartesianPhase parameters radius cell _
    ((polarPlane_norm radius angle).trans (abs_of_nonneg nonnegative))]

theorem decode_weighted_value {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (positive : 0 < radius) (mode : ℤ × ℤ) (value : ComplexEuclidean dimension) :
    (originalRowWeight parameters power radius mode : ℂ)⁻¹ •
      (((annularFrequency mode.1 mode.2 : ℂ) ^ power) •
        (Real.sqrt radius • (Real.exp (radialPhase parameters radius mode.2) • value))) = value := by
  rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul, smul_smul]
  have scalar : (originalRowWeight parameters power radius mode : ℂ)⁻¹ *
      ((annularFrequency mode.1 mode.2 : ℂ) ^ power *
        ((Real.sqrt radius : ℂ) * (Real.exp (radialPhase parameters radius mode.2) : ℂ))) = 1 := by
    have weightNe : (originalRowWeight parameters power radius mode : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (originalRowWeight_pos parameters power radius positive mode).ne'
    apply (inv_mul_eq_one₀ weightNe).mpr
    unfold originalRowWeight
    push_cast
    ring
  simp only [mul_assoc, scalar, one_smul]

theorem decode_weighted_angular {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (positive : 0 < radius) (mode : ℤ × ℤ) (field : ℝ → ComplexEuclidean dimension) :
    (originalRowWeight parameters power radius mode : ℂ)⁻¹ •
      (((annularFrequency mode.1 mode.2 : ℂ) ^ power) • (Real.sqrt radius •
        angularCoefficient (fun angle => cartesianWeight parameters mode.2 (polarPlane (radius, angle)) •
          field angle) mode.1)) = angularCoefficient field mode.1 := by
  simp only [cartesianWeight_polar parameters mode.2 radius _ positive.le]
  have coefficient : angularCoefficient
      (fun angle => Real.exp (radialPhase parameters radius mode.2) • field angle) mode.1 =
        Real.exp (radialPhase parameters radius mode.2) • angularCoefficient field mode.1 := by
    have functionLaw : (fun angle => Real.exp (radialPhase parameters radius mode.2) • field angle) =
        (Real.exp (radialPhase parameters radius mode.2) : ℂ) • field := by
      funext angle
      exact (Complex.coe_smul _ _).symm
    rw [functionLaw, angularCoefficient_smul_continuous, Complex.coe_smul]
  rw [coefficient]
  exact decode_weighted_value parameters power radius positive mode _

theorem dividedRow_original_coefficient {dimension grade power : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + 3 ≤ grade)
    (field : AGrade parameters dimension grade)
    (flat : OriginalValueFlat parameters (by omega) field) (mode : ℤ × ℤ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1,
      originalRowCoefficient parameters power lower
        (completedDivisionRow (power := power) (radial := 0) lower positive bounded parameters paid field) radius mode =
      angularCoefficient (fun angle => radius⁻¹ • completedOriginalCell parameters (by omega) mode.2 field
        (polarClosedPoint radius angle (positive.le.trans inside.1) inside.2)) mode.1 := by
  filter_upwards [dividedRow_flat_literal lower positive bounded parameters paid field flat mode]
    with radius literal
  intro inside
  unfold originalRowCoefficient
  rw [literal inside]
  exact decode_weighted_angular parameters power radius (positive.trans_le inside.1) mode _

theorem restrictedRow_original_coefficient {dimension grade power : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power ≤ grade) (large : 3 ≤ grade)
    (field : AGrade parameters dimension grade) (mode : ℤ × ℤ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1,
      originalRowCoefficient parameters power lower
        (completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters (by omega) field) radius mode =
      angularCoefficient (fun angle => completedOriginalCell parameters large mode.2 field
        (polarClosedPoint radius angle (positive.le.trans inside.1) inside.2)) mode.1 := by
  filter_upwards [restrictedRow_literal lower positive bounded parameters paid large field mode]
    with radius literal
  intro inside
  unfold originalRowCoefficient
  rw [literal inside]
  exact decode_weighted_angular parameters power radius (positive.trans_le inside.1) mode _

end Grad.SourceCollarFullSource
