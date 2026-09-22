import AJF12RealSourceApplicationDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open scoped ContDiff BigOperators
namespace Grad.AnnularOrbitGenerators
open Grad.AnnularKernelOrbit Grad.AnnularInverseCalculus

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Fixed real continuous linear maps commute with every actual ordered
parameter derivative, retaining the original order of differentiation. -/
theorem orderedOrbitDerivative_map (mapping : E →L[ℝ] F) (function : OrbitParameter → E)
    (smooth : ContDiff ℝ ∞ function) (word : List Bool) (point : OrbitParameter) :
    orderedOrbitDerivative word (fun tau => mapping (function tau)) point =
      mapping (orderedOrbitDerivative word function point) := by
  induction word generalizing point with
  | nil => rfl
  | cons axis tail induction =>
    have same : orderedOrbitDerivative tail (fun tau => mapping (function tau)) =
        fun tau => mapping (orderedOrbitDerivative tail function tau) := funext induction
    change fderiv ℝ (orderedOrbitDerivative tail (fun tau => mapping (function tau))) point (axisVector axis) = _
    rw [same]
    have derivative := mapping.hasFDerivAt.comp point
      (((orderedOrbitDerivative_contDiff function smooth tail).differentiable (by simp)) point).hasFDerivAt
    have equality := congrArg (fun linear : OrbitParameter →L[ℝ] F => linear (axisVector axis)) derivative.fderiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, orderedOrbitDerivative] using equality

/-- The composition estimate is for actual derivatives of actual bounded
operators; it preserves the order of the two noncommuting factors. -/
theorem iteratedDeriv_realComposition_bound (outer : ℝ → F →L[ℝ] G) (inner : ℝ → E →L[ℝ] F)
    (outerSmooth : ContDiff ℝ ∞ outer) (innerSmooth : ContDiff ℝ ∞ inner) (order : ℕ) (time : ℝ) :
    ‖iteratedDeriv order (fun parameter => (outer parameter).comp (inner parameter)) time‖ ≤
      ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
        ‖iteratedDeriv index outer time‖ * ‖iteratedDeriv (order - index) inner time‖ := by
  have bound := (ContinuousLinearMap.compL ℝ E F G).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    outerSmooth innerSmooth time (n := order) (by exact_mod_cast (show (order : ℕ∞) ≤ ⊤ from le_top))
    (ContinuousLinearMap.norm_compL_le ℝ E F G)
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, ContinuousLinearMap.compL_apply] using bound

end Grad.AnnularOrbitGenerators
