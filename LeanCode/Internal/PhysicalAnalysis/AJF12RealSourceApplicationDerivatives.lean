import AJB23ActualAxisDerivativeRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff
namespace Grad.AnnularOrbitGenerators
open Grad.AnnularKernelOrbit Grad.AnnularInverseCalculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The full shared source carrier is real. Its genuine application
derivatives obey the same binomial norm estimate without a complex structure
on the independently prescribed real radial source graphs. -/
theorem iteratedDeriv_realOperatorApplication_bound (operator : ℝ → E →L[ℝ] F) (data : ℝ → E)
    (operatorSmooth : ContDiff ℝ ∞ operator) (dataSmooth : ContDiff ℝ ∞ data)
    (order : ℕ) (time : ℝ) :
    ‖iteratedDeriv order (fun parameter => operator parameter (data parameter)) time‖ ≤
      ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
        ‖iteratedDeriv index operator time‖ * ‖iteratedDeriv (order - index) data time‖ := by
  have bound := (ContinuousLinearMap.id ℝ (E →L[ℝ] F)).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    operatorSmooth dataSmooth time (n := order) (by exact_mod_cast (show (order : ℕ∞) ≤ ⊤ from le_top))
    ContinuousLinearMap.norm_id_le
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, ContinuousLinearMap.id_apply] using bound

theorem iteratedDeriv_realOperatorAxisApplication_bound (operator : OrbitParameter → E →L[ℝ] F) (data : ℝ → E)
    (operatorSmooth : ContDiff ℝ ∞ operator) (dataSmooth : ContDiff ℝ ∞ data)
    (axis : Bool) (order : ℕ) (time : ℝ) :
    ‖iteratedDeriv order (fun parameter => operator (parameter • axisVector axis) (data parameter)) time‖ ≤
      ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
        ‖orderedOrbitDerivative (List.replicate index axis) operator (time • axisVector axis)‖ *
        ‖iteratedDeriv (order - index) data time‖ := by
  have lineSmooth : ContDiff ℝ ∞ (fun parameter : ℝ => operator (parameter • axisVector axis)) :=
    operatorSmooth.comp (contDiff_id.smul contDiff_const)
  have bound := iteratedDeriv_realOperatorApplication_bound (fun parameter => operator (parameter • axisVector axis))
    data lineSmooth dataSmooth order time
  have actual (index : ℕ) :
      iteratedDeriv index (fun parameter : ℝ => operator (parameter • axisVector axis)) time =
        orderedOrbitDerivative (List.replicate index axis) operator (time • axisVector axis) := by
    simpa only [zero_add] using iteratedDeriv_axis_restriction operator operatorSmooth axis 0 index time
  simpa only [actual] using bound

end Grad.AnnularOrbitGenerators
