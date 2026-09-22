import SCD28GraphFaithfulness

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState

/-- Undo only the isometric sqrt(r) storage convention. -/
def radialValue {dimension : ℕ} (lower : ℝ) (field : RadialL2 dimension lower)
    (radius : ℝ) : ComplexEuclidean dimension :=
  reciprocalRadialWeight lower (fun _ => 1) radius • field radius

theorem radialValue_norm_sq {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : RadialL2 dimension lower) :
    ‖field‖ ^ 2 = ∫ radius in lower..1, radius * ‖radialValue lower field radius‖ ^ 2 := by
  rw [radialLp_norm_sq, intervalIntegral.integral_of_le bounded, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
  have rootPositive := Real.sqrt_pos.2 (positive.trans_le inside.1)
  rw [radialValue, norm_smul, Real.norm_eq_abs, reciprocalRadialWeight,
    max_eq_right inside.1, one_div, abs_of_pos (inv_pos.2 rootPositive), mul_pow]
  have rootSquare := Real.sq_sqrt (positive.le.trans inside.1)
  field_simp
  nlinarith

theorem divisionRow_norm_sq {dimension : ℕ} (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (field : DivisionRow dimension lower) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ,
      ∫ radius in lower..1, radius * ‖radialValue lower (field mode) radius‖ ^ 2 := by
  have equality := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at equality
  rw [equality]
  apply tsum_congr
  intro mode
  exact radialValue_norm_sq lower positive bounded (field mode)

/-- The complete graph norm is exactly the original sum of radial L2(r dr)
norms. Nu^p is carried by every graph coordinate, including its weak derivatives. -/
theorem annularDerivativeGraph_norm {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : annularDerivativeGraph dimension lower positive radial) :
    ‖field‖ = ∑ index : Fin (radial + 1), Real.sqrt (∑' mode : ℤ × ℤ,
      ∫ radius in lower..1, radius * ‖radialValue lower (field.val index mode) radius‖ ^ 2) := by
  change ‖field.val‖ = _
  rw [PiLp.norm_eq_of_L1]
  apply Finset.sum_congr rfl
  intro index _
  rw [← divisionRow_norm_sq lower positive bounded, Real.sqrt_sq (norm_nonneg _)]

theorem completedDivision_core_norm {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ) (field : ACore parameters dimension) :
    ‖completedDivision lower positive bounded parameters power radial
      (aGradeEta parameters (GradeCore.ofCoreLinear field))‖ =
      originalDivisionGraphNorm lower power radial parameters field :=
  completedDivisionArray_core_norm lower positive bounded parameters power radial field

end Grad.SourceCollarDivision
