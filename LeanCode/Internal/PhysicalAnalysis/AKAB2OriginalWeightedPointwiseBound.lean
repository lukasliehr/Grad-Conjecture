import AKAB1RadialShellCauchy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Grad.WeightedAxisRemoval
open Grad.CartesianState Grad.PhaseAlgebra Grad.SourceCollarDivision
open Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.ClosedJets

theorem originalPhaseWeight_one_le (parameters : PhaseParameters) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (cell : ℤ) :
    1 ≤ Real.exp (radialPhase parameters radius cell) := by
  have lower : 1 ≤ phaseWeight parameters radius cell :=
    Real.one_le_exp (mul_nonneg (phaseWidth_nonneg parameters radius nonnegative bounded) (abs_nonneg _))
  exact lower.trans (phaseWeight_le_exp_radialPhase parameters radius nonnegative bounded cell)

/-- The exact common storage is r^(-7/4) exp(Phi). Unweighting it loses
no original analytic width and gives the radial power used by ER2. -/
theorem lowRhoPhysicalWeight_inverse_bound (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    (lowRhoPhysicalWeight parameters lower positive radius mode)⁻¹ ≤ radius ^ (7 / 4 : ℝ) := by
  have radiusPositive := positive.trans_le inside.1
  have phaseBound := originalPhaseWeight_one_le parameters radius radiusPositive.le inside.2 mode.2
  have storage : (lowStorageWeight lower positive radius)⁻¹ = radius ^ (7 / 4 : ℝ) := by
    change ((max lower radius) ^ (-(7 / 4 : ℝ)))⁻¹ = _
    rw [max_eq_right inside.1, Real.rpow_neg radiusPositive.le, inv_inv]
  rw [lowRhoPhysicalWeight, mul_inv_rev, storage]
  exact (mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ phaseBound)
    (Real.rpow_nonneg radiusPositive.le _)).trans_eq (one_mul _)

theorem lowRhoPhysicalCoefficient_norm_bound {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (field : DivisionRow dimension lower)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    ‖lowRhoPhysicalCoefficient parameters lower positive field radius mode‖ ≤
      radius ^ (7 / 4 : ℝ) * ‖field mode radius‖ := by
  rw [lowRhoPhysicalCoefficient, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (lowRhoPhysicalWeight_pos parameters lower positive radius mode).le]
  exact mul_le_mul_of_nonneg_right
    (lowRhoPhysicalWeight_inverse_bound parameters lower positive radius inside mode) (norm_nonneg _)

end Grad.WeightedAxisRemoval
