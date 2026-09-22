import AJB23ActualAxisDerivativeRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped ContDiff
namespace Grad.AnnularOrbitGenerators
open Grad.AnnularKernelOrbit Grad.AnnularInverseCalculus Grad.AnnularHighInverseOrbit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (jet : ℕ → ℕ → OrbitParameter → E)
  (derivative : ∀ angular cell point, HasFDerivAt (jet angular cell)
    (orbitColumns (jet (angular + 1) cell point) (jet angular (cell + 1) point)) point)

include derivative

theorem jetAxis_hasDerivAt (axis : Bool) (angular cell : ℕ) (time : ℝ) :
    HasDerivAt (fun parameter : ℝ => jet angular cell (parameter • axisVector axis))
      (if axis then jet angular (cell + 1) (time • axisVector axis)
        else jet (angular + 1) cell (time • axisVector axis)) time := by
  have actual := (derivative angular cell (time • axisVector axis)).comp_hasDerivAt time
    ((hasDerivAt_id time).smul_const (axisVector axis))
  cases axis <;> simpa only [Function.comp_def, id_eq, one_smul, axisVector, Bool.false_eq_true, if_false, if_true,
    orbitColumns_apply, Prod.fst, Prod.snd, zero_smul, one_smul, zero_add, add_zero] using actual

theorem iteratedDeriv_jet_angular (angular cell order : ℕ) (time : ℝ) :
    iteratedDeriv order (fun parameter : ℝ => jet angular cell (parameter • axisVector false)) time =
      jet (angular + order) cell (time • axisVector false) := by
  induction order generalizing angular cell time with
  | zero => simp only [iteratedDeriv_zero, Nat.add_zero]
  | succ order induction =>
    have same : iteratedDeriv order (fun parameter : ℝ => jet angular cell (parameter • axisVector false)) =
        fun parameter => jet (angular + order) cell (parameter • axisVector false) := funext (induction angular cell)
    rw [iteratedDeriv_succ, same]
    have actual := (jetAxis_hasDerivAt jet derivative false (angular + order) cell time).deriv
    simpa only [Bool.false_eq_true, if_false, Nat.add_assoc] using actual

theorem iteratedDeriv_jet_cell (angular cell order : ℕ) (time : ℝ) :
    iteratedDeriv order (fun parameter : ℝ => jet angular cell (parameter • axisVector true)) time =
      jet angular (cell + order) (time • axisVector true) := by
  induction order generalizing angular cell time with
  | zero => simp only [iteratedDeriv_zero, Nat.add_zero]
  | succ order induction =>
    have same : iteratedDeriv order (fun parameter : ℝ => jet angular cell (parameter • axisVector true)) =
        fun parameter => jet angular (cell + order) (parameter • axisVector true) := funext (induction angular cell)
    rw [iteratedDeriv_succ, same]
    have actual := (jetAxis_hasDerivAt jet derivative true angular (cell + order) time).deriv
    simpa only [if_true, Nat.add_assoc] using actual

theorem iteratedDeriv_jet_axis (axis : Bool) (order : ℕ) (time : ℝ) :
    iteratedDeriv order (fun parameter : ℝ => jet 0 0 (parameter • axisVector axis)) time =
      jet (if axis then 0 else order) (if axis then order else 0) (time • axisVector axis) := by
  cases axis
  · simpa only [Bool.false_eq_true, if_false, Nat.zero_add] using iteratedDeriv_jet_angular jet derivative 0 0 order time
  · simpa only [if_true, Nat.zero_add] using iteratedDeriv_jet_cell jet derivative 0 0 order time

end Grad.AnnularOrbitGenerators
