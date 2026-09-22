import AKBZ4ActualPositiveCoefficientOrderPayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.GaugeCoefficients.Physical.Allocation Grad.NonlinearProduct

/-- CT9 for the complete positive-order sum, in the original mixed norm.
The same low norm occurs in every high-coefficient term. -/
theorem originalPositiveOrderSum_oneHigh
    (offset grade : ℕ) (gradePositive : 0<grade) (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ remainder : ℝ, 0≤remainder ∧
      ∀ (dimension : ℕ) (parameters : PhaseParameters) (coefficient : ACore parameters 3)
        (rho curvature : ℝ) (unknown : ACore parameters dimension),
      physicalBudget parameters coefficient rho curvature offset≤1 →
      (∑ index : Fin grade,
        (1+physicalBudget parameters coefficient rho curvature (offset+(index.val+1)))*
          originalGradeNorm (grade-(index.val+1)) unknown)≤
        epsilon*originalGradeNorm grade unknown+
          remainder*((1+physicalBudget parameters coefficient rho curvature (offset+grade))*originalGradeNorm 0 unknown) := by
  have deltaPositive : 0<epsilon/(grade:ℝ) := div_pos epsilonPositive (by exact_mod_cast gradePositive)
  have perTerm (index : Fin grade) := originalPositiveOrder_oneHigh offset grade (index.val+1)
    gradePositive (Nat.succ_pos _) (Nat.succ_le_iff.mpr index.isLt) (epsilon/grade) deltaPositive
  choose constants nonnegative estimates using perTerm
  refine ⟨∑ index,constants index,Finset.sum_nonneg (fun index _ => nonnegative index),?_⟩
  intro dimension parameters coefficient rho curvature unknown lowBound
  have factor : (grade:ℝ)*((epsilon/grade)*originalGradeNorm grade unknown)=epsilon*originalGradeNorm grade unknown := by
    field_simp
  calc
    _≤∑ index : Fin grade,
        ((epsilon/grade)*originalGradeNorm grade unknown+
          constants index*((1+physicalBudget parameters coefficient rho curvature (offset+grade))*originalGradeNorm 0 unknown)) :=
      Finset.sum_le_sum (fun index _ => estimates index dimension parameters coefficient rho curvature unknown lowBound)
    _=(grade:ℝ)*((epsilon/grade)*originalGradeNorm grade unknown)+
        (∑ index,constants index)*((1+physicalBudget parameters coefficient rho curvature (offset+grade))*originalGradeNorm 0 unknown) := by
      rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←Finset.sum_mul]
    _=_ := by rw [factor]

end Grad.OriginalCartesianTameEstimate
