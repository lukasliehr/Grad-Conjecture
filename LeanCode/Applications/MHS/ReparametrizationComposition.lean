import ReparametrizationBasic
import Mathlib.Analysis.Calculus.ContDiff.Comp

noncomputable section

open Set

namespace Grad.MainAssembly.TargetReparametrization

open Grad.MainTarget

/-- Compose forward target local lifts.  The second lift is chosen at the
actual ambient image of the first, and the source is shrunk to the interior of
the preimage of its open domain. -/
theorem compHasRegularLocalLifts (regularity : Regularity)
    (outer inner : Reference ≃ Reference)
    (outerLifts : HasRegularLocalLifts regularity outer)
    (innerLifts : HasRegularLocalLifts regularity inner) :
    HasRegularLocalLifts regularity (inner.trans outer) := by
  intro point pointInCylinder
  rcases innerLifts point pointInCylinder with
    ⟨innerNeighborhood, innerOpen, pointInInnerNeighborhood,
      innerLift, innerSmooth, innerAgreement⟩
  obtain ⟨innerImageInCylinder, innerAtPoint⟩ :=
    innerAgreement point pointInInnerNeighborhood pointInCylinder
  rcases outerLifts (innerLift point) innerImageInCylinder with
    ⟨outerNeighborhood, outerOpen, innerImageInOuterNeighborhood,
      outerLift, outerSmooth, outerAgreement⟩

  let neighborhood := interior (innerNeighborhood ∩ innerLift ⁻¹' outerNeighborhood)
  have innerNeighborhoodMem : innerNeighborhood ∈ nhds point :=
    innerOpen.mem_nhds pointInInnerNeighborhood
  have innerLiftContinuousAt : ContinuousAt innerLift point :=
    (innerSmooth point pointInInnerNeighborhood).contDiffAt
      innerNeighborhoodMem |>.continuousAt
  have preimageMem : innerLift ⁻¹' outerNeighborhood ∈ nhds point :=
    innerLiftContinuousAt.preimage_mem_nhds
      (outerOpen.mem_nhds innerImageInOuterNeighborhood)
  have pointInNeighborhood : point ∈ neighborhood := by
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.inter_mem innerNeighborhoodMem preimageMem)
  have neighborhoodOpen : IsOpen neighborhood := isOpen_interior
  have compositionSmooth :
      ContDiffOn ℝ regularity.order (outerLift ∘ innerLift) neighborhood := by
    exact (outerSmooth.comp_inter innerSmooth).mono interior_subset

  refine ⟨neighborhood, neighborhoodOpen, pointInNeighborhood,
    outerLift ∘ innerLift, compositionSmooth, ?_⟩
  intro argument argumentInNeighborhood argumentInCylinder
  have argumentInIntersection :
      argument ∈ innerNeighborhood ∩ innerLift ⁻¹' outerNeighborhood :=
    interior_subset argumentInNeighborhood
  obtain ⟨innerArgumentInCylinder, innerAtArgument⟩ :=
    innerAgreement argument argumentInIntersection.1 argumentInCylinder
  obtain ⟨outerImageInCylinder, outerAtArgument⟩ :=
    outerAgreement (innerLift argument) argumentInIntersection.2 innerArgumentInCylinder
  refine ⟨outerImageInCylinder, ?_⟩
  calc
    quotientPoint ((outerLift ∘ innerLift) argument) outerImageInCylinder =
        outer (quotientPoint (innerLift argument) innerArgumentInCylinder) :=
      outerAtArgument
    _ = outer (inner (quotientPoint argument argumentInCylinder)) := by
      rw [innerAtArgument]
    _ = (inner.trans outer) (quotientPoint argument argumentInCylinder) := rfl

/-- Exact `NG_Z06_COMP`: target reparametrizations are closed under the
composition which applies `inner` first and `outer` second, including the
reverse-order inverse lift. -/
theorem compIsReparametrization (regularity : Regularity)
    (outer inner : Reference ≃ Reference)
    (outerRegular : IsReparametrization regularity outer)
    (innerRegular : IsReparametrization regularity inner) :
    IsReparametrization regularity (inner.trans outer) := by
  refine ⟨compHasRegularLocalLifts regularity outer inner
      outerRegular.1 innerRegular.1, ?_⟩
  simpa using compHasRegularLocalLifts regularity inner.symm outer.symm
    innerRegular.2 outerRegular.2

end Grad.MainAssembly.TargetReparametrization
