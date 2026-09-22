import GQC60ExtensionPolynomial

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

def operatorBlockMap {input output : ℕ} (outer : OperatorValue 3 output) (inner : OperatorValue input 3)
    (field : C(ClosedDisk, OperatorValue 3 3)) : C(ClosedDisk, OperatorValue input output) where
  toFun point := (outer.comp (field point)).comp inner
  continuous_toFun := by fun_prop

theorem operator_sandwich_norm_le {input output : ℕ} (outer : OperatorValue 3 output) (inner : OperatorValue input 3)
    (field : OperatorValue 3 3) (outerSmall : ‖outer‖ ≤ 1) (innerSmall : ‖inner‖ ≤ 1) :
    ‖(outer.comp field).comp inner‖ ≤ ‖field‖ := by
  have innerBound := (ContinuousLinearMap.opNorm_comp_le (outer.comp field) inner).trans
    (mul_le_mul_of_nonneg_left innerSmall (norm_nonneg _))
  rw [mul_one] at innerBound
  exact innerBound.trans ((ContinuousLinearMap.opNorm_comp_le outer field).trans
    ((mul_le_mul_of_nonneg_right outerSmall (norm_nonneg _)).trans_eq (one_mul _)))

theorem operatorBlockMap_norm_le {input output : ℕ} (outer : OperatorValue 3 output) (inner : OperatorValue input 3)
    (field : C(ClosedDisk, OperatorValue 3 3)) (outerSmall : ‖outer‖ ≤ 1) (innerSmall : ‖inner‖ ≤ 1) :
    ‖operatorBlockMap outer inner field‖ ≤ ‖field‖ := by
  apply (ContinuousMap.norm_le (operatorBlockMap outer inner field) (norm_nonneg field)).2
  intro point
  exact (operator_sandwich_norm_le outer inner (field point) outerSmall innerSmall).trans (field.norm_coe_le_norm point)

theorem operator_reconstruction_four (field : OperatorValue 3 3) :
    field =
      (planarInclusionMap.comp ((planarPartMap.comp field).comp planarInclusionMap)).comp planarPartMap +
      (planarInclusionMap.comp ((planarPartMap.comp field).comp toroidalInclusionMap)).comp toroidalPartMap +
      ((toroidalInclusionMap.comp ((toroidalPartMap.comp field).comp planarInclusionMap)).comp planarPartMap +
       (toroidalInclusionMap.comp ((toroidalPartMap.comp field).comp toroidalInclusionMap)).comp toroidalPartMap) := by
  have equality : field = (planarInclusionMap.comp planarPartMap + toroidalInclusionMap.comp toroidalPartMap).comp
      (field.comp (planarInclusionMap.comp planarPartMap + toroidalInclusionMap.comp toroidalPartMap)) := by
    rw [splitting_reconstruction]
    simp only [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  exact equality.trans (by
    simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_assoc]
    abel)

theorem operator_norm_four_blocks (field : OperatorValue 3 3) :
    ‖field‖ ≤ ‖(planarPartMap.comp field).comp planarInclusionMap‖ +
      ‖(planarPartMap.comp field).comp toroidalInclusionMap‖ +
      (‖(toroidalPartMap.comp field).comp planarInclusionMap‖ +
       ‖(toroidalPartMap.comp field).comp toroidalInclusionMap‖) := by
  have reconstruction := operator_reconstruction_four field
  have sandwich {input output : ℕ} (outer : OperatorValue input 3) (inner : OperatorValue 3 output)
      (middle : OperatorValue output input) (outerSmall : ‖outer‖ ≤ 1) (innerSmall : ‖inner‖ ≤ 1) :
      ‖(outer.comp middle).comp inner‖ ≤ ‖middle‖ := by
    have first := (ContinuousLinearMap.opNorm_comp_le (outer.comp middle) inner).trans
      (mul_le_mul_of_nonneg_left innerSmall (norm_nonneg _))
    rw [mul_one] at first
    exact first.trans ((ContinuousLinearMap.opNorm_comp_le outer middle).trans
      ((mul_le_mul_of_nonneg_right outerSmall (norm_nonneg _)).trans_eq (one_mul _)))
  exact (congrArg norm reconstruction).trans_le ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans
      (add_le_add (sandwich _ _ _ planarInclusionMap_norm_le planarPartMap_norm_le)
        (sandwich _ _ _ planarInclusionMap_norm_le toroidalPartMap_norm_le)))
      ((norm_add_le _ _).trans
        (add_le_add (sandwich _ _ _ toroidalInclusionMap_norm_le planarPartMap_norm_le)
          (sandwich _ _ _ toroidalInclusionMap_norm_le toroidalPartMap_norm_le)))))

theorem operatorMap_norm_four_blocks (field : C(ClosedDisk, OperatorValue 3 3)) :
    ‖field‖ ≤ ‖operatorBlockMap planarPartMap planarInclusionMap field‖ +
      ‖operatorBlockMap planarPartMap toroidalInclusionMap field‖ +
      (‖operatorBlockMap toroidalPartMap planarInclusionMap field‖ +
       ‖operatorBlockMap toroidalPartMap toroidalInclusionMap field‖) := by
  apply (ContinuousMap.norm_le field (by positivity)).2
  intro point
  exact (operator_norm_four_blocks (field point)).trans
    (add_le_add (add_le_add ((operatorBlockMap planarPartMap planarInclusionMap field).norm_coe_le_norm point)
      ((operatorBlockMap planarPartMap toroidalInclusionMap field).norm_coe_le_norm point))
      (add_le_add ((operatorBlockMap toroidalPartMap planarInclusionMap field).norm_coe_le_norm point)
        ((operatorBlockMap toroidalPartMap toroidalInclusionMap field).norm_coe_le_norm point)))

end Grad.GaugeCoefficients.Physical.Compensated
