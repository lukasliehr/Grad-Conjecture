import ReparametrizationBasic
import Mathlib.Analysis.Calculus.ContDiff.Comp

noncomputable section

open Set

namespace Grad.MainAssembly.TargetReparametrization

open Grad.MainTarget

universe targetUniverse

theorem predecessorOrder_le (regularity : Regularity) :
    regularity.predecessor.order ≤ regularity.order := by
  cases regularity with
  | finite order =>
      simp only [Regularity.predecessor, Regularity.order]
      exact_mod_cast Nat.sub_le order 1
  | smooth =>
      exact le_rfl

/-- Compose a target local extension with a reference local lift whose
regularity order is at least the extension order. -/
theorem hasRegularity_comp_of_order_le
    {Target : Type targetUniverse} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (reparametrizationRegularity mappingRegularity : Regularity)
    (orderBound : mappingRegularity.order ≤ reparametrizationRegularity.order)
    (mapping : Reference → Target) (reparametrization : Reference ≃ Reference)
    (mappingRegular : HasRegularity mappingRegularity mapping)
    (reparametrizationRegular :
      IsReparametrization reparametrizationRegularity reparametrization) :
    HasRegularity mappingRegularity (mapping ∘ reparametrization) := by
  intro point pointInCylinder
  rcases reparametrizationRegular.1 point pointInCylinder with
    ⟨liftNeighborhood, liftOpen, pointInLiftNeighborhood,
      localLift, liftSmooth, liftAgreement⟩
  obtain ⟨liftImageInCylinder, liftAtPoint⟩ :=
    liftAgreement point pointInLiftNeighborhood pointInCylinder
  rcases mappingRegular (localLift point) liftImageInCylinder with
    ⟨mappingNeighborhood, mappingOpen, liftImageInMappingNeighborhood,
      mappingExtension, mappingSmooth, mappingAgreement⟩

  let neighborhood := interior (liftNeighborhood ∩ localLift ⁻¹' mappingNeighborhood)
  have liftNeighborhoodMem : liftNeighborhood ∈ nhds point :=
    liftOpen.mem_nhds pointInLiftNeighborhood
  have liftContinuousAt : ContinuousAt localLift point :=
    (liftSmooth point pointInLiftNeighborhood).contDiffAt liftNeighborhoodMem |>.continuousAt
  have preimageMem : localLift ⁻¹' mappingNeighborhood ∈ nhds point :=
    liftContinuousAt.preimage_mem_nhds
      (mappingOpen.mem_nhds liftImageInMappingNeighborhood)
  have pointInNeighborhood : point ∈ neighborhood := by
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.inter_mem liftNeighborhoodMem preimageMem)
  have weakenedLiftSmooth :
      ContDiffOn ℝ mappingRegularity.order localLift liftNeighborhood :=
    liftSmooth.of_le orderBound
  have compositionSmooth :
      ContDiffOn ℝ mappingRegularity.order
        (mappingExtension ∘ localLift) neighborhood := by
    exact (mappingSmooth.comp_inter weakenedLiftSmooth).mono interior_subset

  refine ⟨neighborhood, isOpen_interior, pointInNeighborhood,
    mappingExtension ∘ localLift, compositionSmooth, ?_⟩
  intro argument argumentInNeighborhood
  rcases argumentInNeighborhood with
    ⟨argumentInNeighborhood, argumentInCylinder⟩
  have argumentInIntersection :
      argument ∈ liftNeighborhood ∩ localLift ⁻¹' mappingNeighborhood :=
    interior_subset argumentInNeighborhood
  obtain ⟨liftArgumentInCylinder, liftAtArgument⟩ :=
    liftAgreement argument argumentInIntersection.1 argumentInCylinder
  calc
    (mappingExtension ∘ localLift) argument =
        periodicLift mapping (localLift argument) :=
      mappingAgreement ⟨argumentInIntersection.2, liftArgumentInCylinder⟩
    _ = mapping (quotientPoint (localLift argument) liftArgumentInCylinder) := by
      simp only [periodicLift, dif_pos liftArgumentInCylinder]
    _ = mapping (reparametrization (quotientPoint argument argumentInCylinder)) := by
      rw [liftAtArgument]
    _ = (mapping ∘ reparametrization) (quotientPoint argument argumentInCylinder) := rfl
    _ = periodicLift (mapping ∘ reparametrization) argument := by
      simp only [periodicLift, dif_pos argumentInCylinder]

theorem hasRegularity_comp
    {Target : Type targetUniverse} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (regularity : Regularity) (mapping : Reference → Target)
    (reparametrization : Reference ≃ Reference)
    (mappingRegular : HasRegularity regularity mapping)
    (reparametrizationRegular : IsReparametrization regularity reparametrization) :
    HasRegularity regularity (mapping ∘ reparametrization) :=
  hasRegularity_comp_of_order_le regularity regularity le_rfl mapping reparametrization
    mappingRegular reparametrizationRegular

theorem predecessorHasRegularity_comp
    {Target : Type targetUniverse} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (regularity : Regularity) (mapping : Reference → Target)
    (reparametrization : Reference ≃ Reference)
    (mappingRegular : HasRegularity regularity.predecessor mapping)
    (reparametrizationRegular : IsReparametrization regularity reparametrization) :
    HasRegularity regularity.predecessor (mapping ∘ reparametrization) :=
  hasRegularity_comp_of_order_le regularity regularity.predecessor
    (predecessorOrder_le regularity) mapping reparametrization
    mappingRegular reparametrizationRegular

end Grad.MainAssembly.TargetReparametrization
