import SCC29CompletedRadialProduct

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarAngular Grad.PhaseAlgebra

/-- The literal isometric coordinate for the manuscript's radial r dr norm. -/
def originalRowWeight (parameters : PhaseParameters) (power : ℕ) (radius : ℝ) (mode : ℤ × ℤ) : ℝ :=
  Real.sqrt radius * Real.exp (radialPhase parameters radius mode.2) * annularFrequency mode.1 mode.2 ^ power

theorem originalRowWeight_pos (parameters : PhaseParameters) (power : ℕ) (radius : ℝ)
    (positive : 0 < radius) (mode : ℤ × ℤ) : 0 < originalRowWeight parameters power radius mode :=
  mul_pos (mul_pos (Real.sqrt_pos.mpr positive) (Real.exp_pos _)) (pow_pos (annularFrequency_pos _ _) _)

def originalRowCoefficient {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ) (lower : ℝ)
    (field : DivisionRow dimension lower) (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean dimension :=
  ((originalRowWeight parameters power radius mode : ℂ)⁻¹) • field mode radius

theorem originalRowCoefficient_weighted {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ) (lower : ℝ)
    (field : DivisionRow dimension lower) (radius : ℝ) (positive : 0 < radius) (mode : ℤ × ℤ) :
    (originalRowWeight parameters power radius mode : ℂ) • originalRowCoefficient parameters power lower field radius mode =
      field mode radius := by
  rw [originalRowCoefficient, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast (originalRowWeight_pos parameters power radius positive mode).ne'

theorem originalRowCoefficient_energy {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ) (lower : ℝ)
    (field : DivisionRow dimension lower) (radius : ℝ) (positive : 0 < radius) (mode : ℤ × ℤ) :
    ‖field mode radius‖ ^ 2 = radius *
      (Real.exp (radialPhase parameters radius mode.2) * annularFrequency mode.1 mode.2 ^ power) ^ 2 *
        ‖originalRowCoefficient parameters power lower field radius mode‖ ^ 2 := by
  rw [← originalRowCoefficient_weighted parameters power lower field radius positive mode, norm_smul,
    Complex.norm_real, Real.norm_of_nonneg (originalRowWeight_pos parameters power radius positive mode).le, mul_pow]
  unfold originalRowWeight
  rw [mul_pow, mul_pow, Real.sq_sqrt positive.le]
  ring

/-- Exact full-cell norm identity: original analytic width, full nu, and
radial L2(r dr), with no equivalent replacement norm. -/
theorem originalRow_norm_sq {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ) (lower : ℝ)
    (positive : 0 < lower) (field : DivisionRow dimension lower) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ,
      ∫ radius, radius * (Real.exp (radialPhase parameters radius mode.2) * annularFrequency mode.1 mode.2 ^ power) ^ 2 *
        ‖originalRowCoefficient parameters power lower field radius mode‖ ^ 2 ∂volume.restrict (Icc lower 1) := by
  rw [radialRow_norm_sq]
  apply tsum_congr
  intro mode
  rw [radialLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
  exact originalRowCoefficient_energy parameters power lower field radius (positive.trans_le inside.1) mode

theorem originalRow_product_scalar (parameters : PhaseParameters) (power : ℕ) (radius : ℝ)
    (positive : 0 < radius) (mode shift : ℤ × ℤ) (coefficient : ℂ) :
    (originalRowWeight parameters power radius mode : ℂ)⁻¹ *
      ((Real.exp (radialPhase parameters radius mode.2 - radialPhase parameters radius (mode - shift).2) : ℂ) *
        (annularFrequency mode.1 mode.2 : ℂ) ^ power * coefficient) =
      coefficient * (originalRowWeight parameters 0 radius (mode - shift) : ℂ)⁻¹ := by
  have squareRoot : (Real.sqrt radius : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr positive).ne'
  have exponential : (Real.exp (radialPhase parameters radius mode.2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos _).ne'
  have sourceExponential : (Real.exp (radialPhase parameters radius (mode - shift).2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos _).ne'
  have frequency : (annularFrequency mode.1 mode.2 : ℂ) ≠ 0 := by exact_mod_cast (annularFrequency_pos _ _).ne'
  unfold originalRowWeight
  rw [Real.exp_sub]
  push_cast
  field_simp

end Grad.SourceCollarCoefficients
