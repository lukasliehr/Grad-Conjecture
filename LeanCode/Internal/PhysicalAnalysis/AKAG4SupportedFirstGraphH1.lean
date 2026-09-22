import AKAG3CompactWeakTemperedDerivative

noncomputable section

set_option maxHeartbeats 300000

open MeasureTheory
open scoped BigOperators

namespace Grad.CartesianStartup

open Grad.PDEBootstrap Grad.WeightedJets Grad.WeightedJets.Ordered Grad.WeightedJets.ZeroExtension

theorem startupOrderedFirst_supported {support : Set Spatial}
    (field : GraphGrade 3 1 0 Set.univ) (supported : TupleSupported 3 1 Set.univ support field.val)
    (direction : Fin 2) :
    SupportedField CellValues Set.univ support
      (orderedDerivative 3 1 1 Set.univ (fun _ => 0) le_rfl field (startupFirstWord direction)) := by
  rw [orderedDerivative_apply]
  change SupportedField CellValues Set.univ support
    (Grad.CellWeights.inverseFieldCLM 3 Set.univ 0 (field.val _))
  rw [Grad.CellWeights.inverseFieldCLM_zero, ContinuousLinearMap.id_apply]
  exact supported _

theorem startupFirstBase_supported {support : Set Spatial}
    (field : GraphGrade 3 1 0 Set.univ) (supported : TupleSupported 3 1 Set.univ support field.val) :
    SupportedField CellValues Set.univ support (base 3 1 Set.univ (fun _ => 0) field) :=
  ambientBase_supported 3 1 Set.univ support (fun _ => 0) field.val supported

theorem startupFirstOrdered_weak (field : GraphGrade 3 1 0 Set.univ) (direction : Fin 2) :
    Grad.WeakTesting.Commutation.HasWeakOrderedDerivative 3 Set.univ 1 (startupFirstWord direction)
      (base 3 1 Set.univ (fun _ => 0) field)
      (orderedDerivative 3 1 1 Set.univ (fun _ => 0) le_rfl field (startupFirstWord direction)) :=
  orderedDerivative_hasWeak 3 1 1 Set.univ (fun _ => 0) le_rfl field (startupFirstWord direction)

theorem startupH1_data_exists (field : FieldL2) (derivatives : Fin 2 → FieldL2)
    (equations : ∀ direction, distributionDerivative direction (distributionEmbedding field) =
      distributionEmbedding (derivatives direction)) :
    ∃ regular : FieldH1, valueInclusion regular = field ∧
      ∀ direction, weakDerivative direction regular = derivatives direction :=
  ⟨ofWeakDerivatives field derivatives equations, rfl, fun _ => rfl⟩

theorem startupSupportedFirst_h1_exists {support : Set Spatial} (localizer : TestLocalizer Set.univ support)
    (field : supportedJetSubmodule 3 1 Set.univ support (fun _ => 0)) :
    ∃ regular : FieldH1,
      valueInclusion regular = startupWholePlaneField (base 3 1 Set.univ (fun _ => 0) field.val) ∧
      ∀ direction, weakDerivative direction regular = startupWholePlaneField
        (orderedDerivative 3 1 1 Set.univ (fun _ => 0) le_rfl field.val (startupFirstWord direction)) := by
  have transported := @startupCompactWeak_tempered
  generalize equality : startupWholePlaneField = equivalence at transported ⊢
  clear equality
  as_aux_lemma =>
    exact startupH1_data_exists
      (equivalence (base 3 1 Set.univ (fun _ => 0) field.val))
      (fun direction => equivalence
        (orderedDerivative 3 1 1 Set.univ (fun _ => 0) le_rfl field.val (startupFirstWord direction)))
      (fun direction => transported localizer _ _
        (startupFirstBase_supported field.val field.property)
        (startupOrderedFirst_supported field.val field.property direction) direction
        (startupFirstOrdered_weak field.val direction))

/-- Every realization of these exact first coordinates has the original graph norm. -/
theorem startupSupportedFirstH1_norm_of_coordinates {support : Set Spatial}
    (field : supportedJetSubmodule 3 1 Set.univ support (fun _ => 0))
    (regular : FieldH1)
    (represented : valueInclusion regular = startupWholePlaneField (base 3 1 Set.univ (fun _ => 0) field.val))
    (coordinates : ∀ direction, weakDerivative direction regular = startupWholePlaneField
      (orderedDerivative 3 1 1 Set.univ (fun _ => 0) le_rfl field.val (startupFirstWord direction))) :
    ‖regular‖ = ‖field‖ := by
  generalize equality : startupWholePlaneField = equivalence at represented coordinates
  clear equality
  as_aux_lemma =>
    let zeroth := base 3 1 Set.univ (fun _ => 0) field.val
    let derivatives (direction : Fin 2) :=
      orderedDerivative 3 1 1 Set.univ (fun _ => 0) le_rfl field.val (startupFirstWord direction)
    have weak (direction : Fin 2) := startupFirstOrdered_weak field.val direction
    have reconstructed : startupFirstGraph zeroth derivatives weak = field.val := by
      apply base_injective 3 1 Set.univ isOpen_univ (fun _ => 0)
      rw [startupFirstGraph_base]
    have square := startupFirstGraph_norm_sq zeroth derivatives weak
    rw [reconstructed] at square
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [fieldH1_norm_sq, represented]
    simp_rw [coordinates, LinearIsometryEquiv.norm_map]
    rw [Fin.sum_univ_two]
    change ‖zeroth‖ ^ 2 + (‖derivatives 0‖ ^ 2 + ‖derivatives 1‖ ^ 2) = ‖field.val‖ ^ 2
    exact (add_assoc _ _ _).symm.trans square.symm

/-- The SAME supported first graph has a whole-plane H1 realization with exact norm. -/
theorem startupSupportedFirst_h1_exists_norm {support : Set Spatial}
    (localizer : TestLocalizer Set.univ support)
    (field : supportedJetSubmodule 3 1 Set.univ support (fun _ => 0)) :
    ∃ regular : FieldH1,
      valueInclusion regular = startupWholePlaneField (base 3 1 Set.univ (fun _ => 0) field.val) ∧
      (∀ direction, weakDerivative direction regular = startupWholePlaneField
        (orderedDerivative 3 1 1 Set.univ (fun _ => 0) le_rfl field.val (startupFirstWord direction))) ∧
      ‖regular‖ = ‖field‖ := by
  obtain ⟨regular, represented, coordinates⟩ := startupSupportedFirst_h1_exists localizer field
  exact ⟨regular, represented, coordinates, startupSupportedFirstH1_norm_of_coordinates field regular represented coordinates⟩

end Grad.CartesianStartup
