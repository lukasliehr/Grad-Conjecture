import AJB22ActualOperatorApplicationDerivatives
import AJA19OrderedInverseBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ContDiff BigOperators
namespace Grad.AnnularOrbitGenerators
open Grad.AnnularKernelOrbit Grad.AnnularInverseCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem orderedOrbitDerivative_contDiff (function : OrbitParameter → E)
    (smooth : ContDiff ℝ ∞ function) (word : List Bool) :
    ContDiff ℝ ∞ (orderedOrbitDerivative word function) := by
  induction word with
  | nil => exact smooth
  | cons axis tail induction =>
    exact (induction.fderiv_right (by simp)).clm_apply contDiff_const

/-- Restricting the genuine full parameter derivative to a coordinate line
produces the actual iterated one-variable derivative, with the same order. -/
theorem iteratedDeriv_axis_restriction (function : OrbitParameter → E)
    (smooth : ContDiff ℝ ∞ function) (axis : Bool) (base : OrbitParameter)
    (order : ℕ) (time : ℝ) :
    iteratedDeriv order (fun parameter : ℝ => function (base + parameter • axisVector axis)) time =
      orderedOrbitDerivative (List.replicate order axis) function (base + time • axisVector axis) := by
  induction order generalizing time with
  | zero => rfl
  | succ order induction =>
    have same : iteratedDeriv order (fun parameter : ℝ => function (base + parameter • axisVector axis)) =
        fun parameter => orderedOrbitDerivative (List.replicate order axis) function (base + parameter • axisVector axis) :=
      funext induction
    rw [iteratedDeriv_succ, same]
    have derivative := (((orderedOrbitDerivative_contDiff function smooth (List.replicate order axis)).differentiable
      (by simp)) (base + time • axisVector axis)).hasFDerivAt.comp_hasDerivAt time
      (((hasDerivAt_id time).smul_const (axisVector axis)).const_add base)
    simpa only [List.replicate_succ, orderedOrbitDerivative, one_smul, Function.comp_def, id_eq] using derivative.deriv

/-- The original cell line has exactly the repeated actual cell derivative. -/
theorem iteratedDeriv_cell_restriction (function : OrbitParameter → E)
    (smooth : ContDiff ℝ ∞ function) (order : ℕ) (time : ℝ) :
    iteratedDeriv order (fun parameter : ℝ => function (0, parameter)) time =
      orderedOrbitDerivative (List.replicate order true) function (0, time) := by
  simpa only [axisVector, if_true, Prod.smul_mk, smul_eq_mul, mul_zero, mul_one, zero_add] using
    iteratedDeriv_axis_restriction function smooth true 0 order time


/-- Binomial application estimate after genuine coordinate-line restriction. -/
theorem iteratedDeriv_operatorCellApplication_bound {F : Type*}
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    (operator : OrbitParameter → E →L[ℂ] F) (data : ℝ → E)
    (operatorSmooth : ContDiff ℝ ∞ operator) (dataSmooth : ContDiff ℝ ∞ data)
    (order : ℕ) (time : ℝ) :
    ‖iteratedDeriv order (fun parameter => operator (0, parameter) (data parameter)) time‖ ≤
      ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
        ‖orderedOrbitDerivative (List.replicate index true) operator (0, time)‖ *
        ‖iteratedDeriv (order - index) data time‖ := by
  have bound := iteratedDeriv_operatorApplication_bound (fun parameter => operator (0, parameter)) data
    (operatorSmooth.comp (contDiff_const.prodMk contDiff_id)) dataSmooth order time
  simpa only [iteratedDeriv_cell_restriction _ operatorSmooth] using bound

end Grad.AnnularOrbitGenerators
