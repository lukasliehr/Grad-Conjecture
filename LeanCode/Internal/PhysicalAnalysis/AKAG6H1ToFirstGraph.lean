import AKAG5TemperedCompactWeakConverse

noncomputable section

set_option maxHeartbeats 300000

open MeasureTheory
open scoped BigOperators

namespace Grad.CartesianStartup

open Grad.PDEBootstrap Grad.WeightedJets

theorem startupFirstGraph_data_exists
    (field : Grad.GenericCarriers.FieldL2 3 Set.univ)
    (derivatives : Fin 2 → Grad.GenericCarriers.FieldL2 3 Set.univ)
    (weak : ∀ direction, Grad.WeakTesting.Commutation.HasWeakOrderedDerivative 3 Set.univ 1
      (startupFirstWord direction) field (derivatives direction)) :
    ∃ graph : GraphGrade 3 1 0 Set.univ,
      base 3 1 Set.univ (fun _ => 0) graph = field ∧
      ‖graph‖ ^ 2 = ‖field‖ ^ 2 + ‖derivatives 0‖ ^ 2 + ‖derivatives 1‖ ^ 2 :=
  ⟨startupFirstGraph field derivatives weak, startupFirstGraph_base _ _ _, startupFirstGraph_norm_sq _ _ _⟩

theorem startupH1_firstGraph_exists_for
    (equivalence : Grad.GenericCarriers.FieldL2 3 Set.univ ≃ₗᵢ[ℂ] FieldL2)
    (transported : ∀ (field derivative : Grad.GenericCarriers.FieldL2 3 Set.univ) (direction : Fin 2),
      distributionDerivative direction (distributionEmbedding (equivalence field)) =
        distributionEmbedding (equivalence derivative) →
      Grad.WeakTesting.Commutation.HasWeakOrderedDerivative 3 Set.univ 1
        (startupFirstWord direction) field derivative)
    (field : FieldH1) :
    ∃ graph : GraphGrade 3 1 0 Set.univ,
      equivalence (base 3 1 Set.univ (fun _ => 0) graph) = valueInclusion field ∧
      ‖graph‖ = ‖field‖ := by
  obtain ⟨graph, represented, square⟩ := startupFirstGraph_data_exists
    (equivalence.symm (valueInclusion field))
    (fun direction => equivalence.symm (weakDerivative direction field))
    (fun direction => transported _ _ direction (by
      rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
      exact (weakDerivative_distribution field direction).symm))
  refine ⟨graph, ?_, ?_⟩
  · rw [represented, LinearIsometryEquiv.apply_symm_apply]
  · apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [LinearIsometryEquiv.norm_map] at square
    have sums : (∑ direction : Fin 2, ‖weakDerivative direction field‖ ^ 2) =
        ‖weakDerivative 0 field‖ ^ 2 + ‖weakDerivative 1 field‖ ^ 2 := Fin.sum_univ_two _
    have target := (fieldH1_norm_sq field).trans
      (congrArg (fun total : ℝ => ‖valueInclusion field‖ ^ 2 + total) sums)
    exact square.trans ((add_assoc _ _ _).trans target.symm)

/-- Every existing H1 field is the SAME original first graph, with exact norm. -/
theorem startupH1_firstGraph_exists (field : FieldH1) :
    ∃ graph : GraphGrade 3 1 0 Set.univ,
      startupWholePlaneField (base 3 1 Set.univ (fun _ => 0) graph) = valueInclusion field ∧
      ‖graph‖ = ‖field‖ :=
  startupH1_firstGraph_exists_for startupWholePlaneField startupTempered_compactWeak field

end Grad.CartesianStartup
