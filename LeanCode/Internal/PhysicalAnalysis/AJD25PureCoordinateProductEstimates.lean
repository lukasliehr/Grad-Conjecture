import AJB23ActualAxisDerivativeRestriction
import AJA13RealOrbitColumns

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped ContDiff BigOperators
namespace Grad.AnnularCrossOrbit
open Grad.AnnularKernelOrbit Grad.AnnularHighInverseOrbit Grad.AnnularInverseCalculus

/-- Uniform at order zero, one original high budget at every positive order. -/
def coordinateJetWeight (budget : ℕ → ℝ) (order : ℕ) : ℝ := if order = 0 then 1 else budget order

theorem coordinateJetWeight_nonnegative (budget : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ budget n) (order : ℕ) :
    0 ≤ coordinateJetWeight budget order := by
  unfold coordinateJetWeight
  split_ifs
  · norm_num
  · exact nonnegative order

private theorem coordinateJetWeight_pair (budget pair : ℕ → ℝ)
    (nonnegative : ∀ n, 0 ≤ budget n) (pairNonnegative : ∀ n, 0 ≤ pair n)
    (paired : ∀ a b, budget a * budget b ≤ pair (a + b) * budget (a + b))
    (first second : ℕ) (positive : 0 < first + second) :
    coordinateJetWeight budget first * coordinateJetWeight budget second ≤
      (1 + pair (first + second)) * budget (first + second) := by
  by_cases firstZero : first = 0
  · subst first
    have secondNonzero : second ≠ 0 := by omega
    have scalar : budget second ≤ (1 + pair second) * budget second :=
      le_mul_of_one_le_left (nonnegative second) (by linarith only [pairNonnegative second])
    simpa [coordinateJetWeight, secondNonzero] using scalar
  by_cases secondZero : second = 0
  · subst second
    have scalar : budget first ≤ (1 + pair first) * budget first :=
      le_mul_of_one_le_left (nonnegative first) (by linarith only [pairNonnegative first])
    simpa [coordinateJetWeight, firstZero] using scalar
  simp only [coordinateJetWeight, if_neg firstZero, if_neg secondZero]
  exact (paired first second).trans (mul_le_mul_of_nonneg_right (by linarith) (nonnegative _))

section Bilinear
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The actual real-parameter derivative of an arbitrary bounded bilinear
operation has the binomial norm estimate, also for complex operator composition. -/
theorem iteratedDeriv_bilinear_bound (product : E →L[ℝ] F →L[ℝ] G)
    (first : ℝ → E) (second : ℝ → F) (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second)
    (order : ℕ) (time : ℝ) :
    ‖iteratedDeriv order (fun t => product (first t) (second t)) time‖ ≤
      ‖product‖ * ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
        ‖iteratedDeriv index first time‖ * ‖iteratedDeriv (order - index) second time‖ := by
  have bound := product.norm_iteratedFDeriv_le_of_bilinear firstSmooth secondSmooth time (n := order)
    (by exact_mod_cast (show (order : ℕ∞) ≤ ⊤ from le_top))
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using bound

/-- Actual bilinear composition preserves one high factor. The displayed
constants may be fixed before any radius, state, or translation is chosen. -/
theorem iteratedDeriv_bilinear_oneHigh (product : E →L[ℝ] F →L[ℝ] G)
    (first : ℝ → E) (second : ℝ → F) (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second)
    (budget pair firstConstant secondConstant : ℕ → ℝ)
    (budgetNonnegative : ∀ n, 0 ≤ budget n) (pairNonnegative : ∀ n, 0 ≤ pair n)
    (firstNonnegative : ∀ n, 0 ≤ firstConstant n) (secondNonnegative : ∀ n, 0 ≤ secondConstant n)
    (paired : ∀ a b, budget a * budget b ≤ pair (a + b) * budget (a + b))
    (order : ℕ) (positive : 0 < order) (time : ℝ)
    (firstBound : ∀ index, index ≤ order → ‖iteratedDeriv index first time‖ ≤ firstConstant index * coordinateJetWeight budget index)
    (secondBound : ∀ index, index ≤ order → ‖iteratedDeriv index second time‖ ≤ secondConstant index * coordinateJetWeight budget index) :
    ‖iteratedDeriv order (fun t => product (first t) (second t)) time‖ ≤
      (‖product‖ * ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
        firstConstant index * secondConstant (order - index) * (1 + pair order)) * budget order := by
  apply (iteratedDeriv_bilinear_bound product first second firstSmooth secondSmooth order time).trans
  rw [mul_assoc, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg product)
  apply Finset.sum_le_sum
  intro index member
  have indexLe : index ≤ order := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp member)
  have complementLe : order - index ≤ order := Nat.sub_le _ _
  have total : index + (order - index) = order := Nat.add_sub_of_le indexLe
  have factors := mul_le_mul (firstBound index indexLe) (secondBound (order - index) complementLe)
    (norm_nonneg _) (mul_nonneg (firstNonnegative index) (coordinateJetWeight_nonnegative budget budgetNonnegative index))
  have budgetProduct := coordinateJetWeight_pair budget pair budgetNonnegative pairNonnegative paired index (order - index) (by omega)
  rw [total] at budgetProduct
  have rearranged : ‖iteratedDeriv index first time‖ * ‖iteratedDeriv (order - index) second time‖ ≤
      (firstConstant index * secondConstant (order - index)) *
        (coordinateJetWeight budget index * coordinateJetWeight budget (order - index)) := factors.trans_eq (by ring)
  have combined := rearranged.trans
    (mul_le_mul_of_nonneg_left budgetProduct (mul_nonneg (firstNonnegative index) (secondNonnegative (order - index))))
  have weighted := mul_le_mul_of_nonneg_left combined (by positivity : (0 : ℝ) ≤ order.choose index)
  simpa only [mul_assoc] using weighted
end Bilinear

section PureJet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Restricting a checked two-column jet to one coordinate gives the
literal iterated one-variable derivative, without a mixed-word consumer. -/
theorem iteratedDeriv_coordinateJet (jet : ℕ → ℕ → OrbitParameter → E)
    (derivative : ∀ angular cell point, HasFDerivAt (jet angular cell)
      (orbitColumns (jet (angular + 1) cell point) (jet angular (cell + 1) point)) point)
    (axis : Bool) (angular cell : ℕ) (base : OrbitParameter) (order : ℕ) (time : ℝ) :
    iteratedDeriv order (fun t : ℝ => jet angular cell (base + t • axisVector axis)) time =
      jet (angular + if axis then 0 else order) (cell + if axis then order else 0) (base + time • axisVector axis) := by
  induction order generalizing time with
  | zero => cases axis <;> rfl
  | succ order induction =>
    have same := funext induction
    rw [iteratedDeriv_succ, same]
    have actual := (derivative (angular + if axis then 0 else order) (cell + if axis then order else 0)
      (base + time • axisVector axis)).comp_hasDerivAt time
      (((hasDerivAt_id time).smul_const (axisVector axis)).const_add base)
    cases axis <;>
      simpa only [axisVector, Bool.false_eq_true, ↓reduceIte, Function.comp_def, id_eq,
        one_smul, orbitColumns_apply, zero_smul, add_zero, zero_add, Nat.add_assoc] using actual.deriv
end PureJet
end Grad.AnnularCrossOrbit
