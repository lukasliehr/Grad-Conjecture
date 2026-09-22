import AKDP81GenericCompactRankEstimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.WeightedJets.Ordered Grad.CellWeights

theorem startupGraph_coordinate_ordered_norm {dimension order : ℕ}
    (graph : GraphGrade dimension order 0 openUnitDisk) (index : JetIndex order) :
    ‖graph.val index‖≤‖orderedDerivative dimension order (degree index) openUnitDisk (fun _ => 0) (degree_le index) graph‖ := by
  let zeros : Fin (degree index+1) := ⟨index.val.1,by change index.val.1 < index.val.1+index.val.2+1; omega⟩
  let word := Grad.OrderedMultiplicity.canonicalWord (degree index) zeros
  have indexSame : wordIndex (degree_le index) word=index := by
    change topIndex (degree_le index) (Grad.OrderedMultiplicity.countZeros (Grad.OrderedMultiplicity.canonicalWord (degree index) zeros))=index
    rw [Grad.OrderedMultiplicity.canonical_count]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change index.val.1+index.val.2-index.val.1=index.val.2
      omega
  have bound := PiLp.norm_apply_le (orderedDerivative dimension order (degree index) openUnitDisk (fun _ => 0) (degree_le index) graph) word
  rw [orderedDerivative_apply,indexSame,Realization.recoveredDerivative_apply,inverseFieldCLM_zero,ContinuousLinearMap.id_apply] at bound
  exact bound

/-- The full ordinary graph consists of its top ordered derivatives and
the same lower graph. This includes every stored lower coordinate. -/
theorem startupFullGraph_top_lower_norm {dimension grade : ℕ}
    (graph : GraphGrade dimension grade 0 openUnitDisk) (lower : GraphGrade dimension (grade-1) 0 openUnitDisk)
    (same : base dimension grade openUnitDisk (fun _ => 0) graph=base dimension (grade-1) openUnitDisk (fun _ => 0) lower) :
    ‖graph‖≤(Fintype.card (JetIndex grade) : ℝ)*‖orderedDerivative dimension grade grade openUnitDisk (fun _ => 0) le_rfl graph‖+
      (∑ index : JetIndex grade,Real.sqrt ((degree index).factorial : ℝ))*‖lower‖ := by
  have each (index : JetIndex grade) : ‖graph.val index‖≤
      ‖orderedDerivative dimension grade grade openUnitDisk (fun _ => 0) le_rfl graph‖+
        Real.sqrt ((degree index).factorial : ℝ)*‖lower‖ := by
    have coordinate := startupGraph_coordinate_ordered_norm graph index
    by_cases top : degree index=grade
    · have atTop : ‖graph.val index‖≤‖orderedDerivative dimension grade grade openUnitDisk (fun _ => 0) le_rfl graph‖ := by
        let rankNorm (rank : {n : ℕ // n≤grade}) : ℝ :=
          ‖orderedDerivative dimension grade rank.val openUnitDisk (fun _ => 0) rank.property graph‖
        have ranks : (⟨degree index,degree_le index⟩ : {n : ℕ // n≤grade})=⟨grade,le_rfl⟩ := Subtype.ext top
        exact coordinate.trans_eq (congrArg rankNorm ranks)
      exact atTop.trans (le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)))
    · have strict : degree index≤grade-1 := by have bounded := degree_le index; omega
      rw [startupOrderedDerivative_sameBase graph (degree_le index) lower strict same] at coordinate
      have lowerBound := orderedDerivative_norm_le dimension (grade-1) (degree index) openUnitDisk (fun _ => 0) strict lower
      exact (coordinate.trans lowerBound).trans (le_add_of_nonneg_left (norm_nonneg _))
  have finite := startupFiniteHilbert_norm_le_sum (fun index : JetIndex grade => graph.val index)
  change ‖graph‖≤_ at finite
  exact (finite.trans (Finset.sum_le_sum (fun index _ => each index))).trans_eq
    (by rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.sum_mul])

end Grad.CartesianStartup
