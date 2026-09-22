import ReparametrizationHomeomorphConsumer
import ReparametrizationDerivativeConsumer

noncomputable section

open Set
open scoped ContDiff Topology

namespace Grad.MainAssembly.TargetReparametrization

open Grad.MainTarget
open Grad.MainTarget.SemanticBridges

/-- Exact `NG_Z06_EMBEDDING`: precomposition by a target
reparametrization preserves the literal target regular embedding predicate. -/
theorem isEmbeddingOfRegularity_comp
    (regularity : Regularity) (admissible : regularity.admissible)
    (mapping : Reference → Vec) (reparametrization : Reference ≃ Reference)
    (mappingEmbedding : IsEmbeddingOfRegularity regularity mapping)
    (isReparametrization : IsReparametrization regularity reparametrization) :
    IsEmbeddingOfRegularity regularity (mapping ∘ reparametrization) := by
  refine ⟨hasRegularity_comp regularity mapping reparametrization
      mappingEmbedding.1 isReparametrization, ?_, ?_⟩
  · exact mappingEmbedding.2.1.comp
      (Consumer.reparametrization_isEmbedding regularity reparametrization
        isReparametrization)
  · intro point pointInCylinder
    rcases isReparametrization.1 point pointInCylinder with
      ⟨liftNeighborhood, liftOpen, pointInLiftNeighborhood,
        localLift, liftSmooth, liftAgreement⟩
    obtain ⟨liftImageInCylinder, liftAtPoint⟩ :=
      liftAgreement point pointInLiftNeighborhood pointInCylinder
    rcases mappingEmbedding.1 (localLift point) liftImageInCylinder with
      ⟨mappingNeighborhood, mappingOpen, liftImageInMappingNeighborhood,
        mappingExtension, mappingSmooth, mappingAgreement⟩

    let neighborhood := interior (liftNeighborhood ∩ localLift ⁻¹' mappingNeighborhood)
    have liftNeighborhoodMem : liftNeighborhood ∈ nhds point :=
      liftOpen.mem_nhds pointInLiftNeighborhood
    have liftContinuousAt : ContinuousAt localLift point :=
      (liftSmooth point pointInLiftNeighborhood).contDiffAt liftNeighborhoodMem
        |>.continuousAt
    have preimageMem : localLift ⁻¹' mappingNeighborhood ∈ nhds point :=
      liftContinuousAt.preimage_mem_nhds
        (mappingOpen.mem_nhds liftImageInMappingNeighborhood)
    have pointInNeighborhood : point ∈ neighborhood := by
      exact mem_interior_iff_mem_nhds.mpr
        (Filter.inter_mem liftNeighborhoodMem preimageMem)
    have compositionSmooth :
        ContDiffOn ℝ regularity.order (mappingExtension ∘ localLift) neighborhood :=
      (mappingSmooth.comp_inter liftSmooth).mono interior_subset
    have compositionAgreement :
        EqOn (mappingExtension ∘ localLift)
          (periodicLift (mapping ∘ reparametrization))
          (neighborhood ∩ cylinder) := by
      intro argument argumentInNeighborhood
      have argumentInIntersection :
          argument ∈ liftNeighborhood ∩ localLift ⁻¹' mappingNeighborhood :=
        interior_subset argumentInNeighborhood.1
      obtain ⟨liftArgumentInCylinder, liftAtArgument⟩ :=
        liftAgreement argument argumentInIntersection.1 argumentInNeighborhood.2
      calc
        (mappingExtension ∘ localLift) argument =
            periodicLift mapping (localLift argument) :=
          mappingAgreement ⟨argumentInIntersection.2, liftArgumentInCylinder⟩
        _ = mapping (quotientPoint (localLift argument) liftArgumentInCylinder) := by
          simp only [periodicLift, dif_pos liftArgumentInCylinder]
        _ = mapping
            (reparametrization (quotientPoint argument argumentInNeighborhood.2)) := by
          rw [liftAtArgument]
        _ = (mapping ∘ reparametrization)
            (quotientPoint argument argumentInNeighborhood.2) := rfl
        _ = periodicLift (mapping ∘ reparametrization) argument := by
          simp only [periodicLift, dif_pos argumentInNeighborhood.2]

    have orderNonzero := regularity_order_ne_zero_of_admissible admissible
    have compositeWithinDerivative :
        fderivWithin ℝ (periodicLift (mapping ∘ reparametrization)) cylinder point =
          fderiv ℝ (mappingExtension ∘ localLift) point :=
      localExtension_fderivWithin uniqueDiffOn_cylinder pointInCylinder
        isOpen_interior pointInNeighborhood compositionSmooth compositionAgreement
        orderNonzero
    have mappingWithinDerivative :
        fderivWithin ℝ (periodicLift mapping) cylinder (localLift point) =
          fderiv ℝ mappingExtension (localLift point) :=
      localExtension_fderivWithin uniqueDiffOn_cylinder liftImageInCylinder
        mappingOpen liftImageInMappingNeighborhood mappingSmooth mappingAgreement
        orderNonzero
    have mappingExtensionInjective :
        Function.Injective (fderiv ℝ mappingExtension (localLift point)) := by
      rw [← mappingWithinDerivative]
      exact mappingEmbedding.2.2 (localLift point) liftImageInCylinder
    have localLiftInjective : Function.Injective (fderiv ℝ localLift point) :=
      Consumer.localLift_fderiv_injective regularity admissible reparametrization
        isReparametrization point pointInCylinder liftNeighborhood liftOpen
        pointInLiftNeighborhood localLift liftSmooth liftAgreement
    have localLiftDifferentiable : DifferentiableAt ℝ localLift point :=
      (liftSmooth point pointInLiftNeighborhood).contDiffAt liftNeighborhoodMem
        |>.differentiableAt orderNonzero
    have mappingExtensionDifferentiable :
        DifferentiableAt ℝ mappingExtension (localLift point) :=
      (mappingSmooth (localLift point) liftImageInMappingNeighborhood).contDiffAt
          (mappingOpen.mem_nhds liftImageInMappingNeighborhood)
        |>.differentiableAt orderNonzero
    rw [compositeWithinDerivative,
      fderiv_comp point mappingExtensionDifferentiable localLiftDifferentiable]
    exact mappingExtensionInjective.comp localLiftInjective

end Grad.MainAssembly.TargetReparametrization
