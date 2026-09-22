import ReparametrizationBasic

noncomputable section

open Set

namespace Grad.MainAssembly.ModuliCurveNonisolation

universe targetUniverse

/-- A point of a real subset that lies in its ambient interior is not isolated
in the subtype topology. -/
theorem not_isOpen_singleton_subtype_of_mem_interior
    {interval : Set ℝ} (parameter : interval)
    (parameterInterior : parameter.val ∈ interior interval) :
    ¬ IsOpen ({parameter} : Set interval) := by
  intro singletonOpen
  change @IsOpen interval
    (TopologicalSpace.induced Subtype.val
      (inferInstance : TopologicalSpace ℝ))
    ({parameter} : Set interval) at singletonOpen
  rcases (isOpen_induced_iff.mp singletonOpen) with
    ⟨ambient, ambientOpen, ambientPreimage⟩
  have ambientIntersection : ambient ∩ interior interval = {parameter.val} := by
    ext point
    constructor
    · intro pointMembership
      have pointInInterval : point ∈ interval :=
        interior_subset pointMembership.2
      have subtypeMembership :
          (⟨point, pointInInterval⟩ : interval) ∈
            Subtype.val ⁻¹' ambient :=
        pointMembership.1
      rw [ambientPreimage] at subtypeMembership
      simpa only [mem_singleton_iff, Subtype.ext_iff] using subtypeMembership
    · intro pointMembership
      have pointEquality : point = parameter.val := by
        simpa only [mem_singleton_iff] using pointMembership
      subst point
      refine ⟨?_, parameterInterior⟩
      have : parameter ∈ Subtype.val ⁻¹' ambient := by
        rw [ambientPreimage]
        exact mem_singleton parameter
      exact this
  have realSingletonOpen : IsOpen ({parameter.val} : Set ℝ) := by
    rw [← ambientIntersection]
    exact ambientOpen.inter isOpen_interior
  exact (not_isOpen_singleton parameter.val) realSingletonOpen

/-- Exact `NG_CAL112`: every neighborhood of a point on a continuous
injective curve contains the image of a distinct nearby parameter, provided
the parameter lies in the ambient interior of its real parameter set. No
separation axiom on the target is used. -/
theorem exists_distinct_image_mem_of_mem_nhds
    {interval : Set ℝ} {Target : Type targetUniverse}
    [TopologicalSpace Target]
    (curve : interval → Target) (curveContinuous : Continuous curve)
    (curveInjective : Function.Injective curve) (parameter : interval)
    (parameterInterior : parameter.val ∈ interior interval)
    {neighborhood : Set Target} (neighborhoodMem : neighborhood ∈ nhds (curve parameter)) :
    ∃ other : interval,
      other ≠ parameter ∧ curve other ∈ neighborhood ∧
        curve other ≠ curve parameter := by
  have preimageMem : curve ⁻¹' neighborhood ∈ nhds parameter :=
    curveContinuous.continuousAt neighborhoodMem
  by_contra noOther
  have preimageSubset : curve ⁻¹' neighborhood ⊆ {parameter} := by
    intro other otherInPreimage
    simp only [mem_singleton_iff]
    by_contra otherNe
    exact noOther ⟨other, otherNe, otherInPreimage,
      fun imageEquality => otherNe (curveInjective imageEquality)⟩
  have singletonMem : ({parameter} : Set interval) ∈ nhds parameter :=
    Filter.mem_of_superset preimageMem preimageSubset
  have singletonOpen : IsOpen ({parameter} : Set interval) := by
    apply isOpen_iff_mem_nhds.mpr
    intro other otherMembership
    have otherEquality : other = parameter := by
      simpa only [mem_singleton_iff] using otherMembership
    subst other
    exact singletonMem
  exact not_isOpen_singleton_subtype_of_mem_interior
    parameter parameterInterior singletonOpen

/-- The neighborhood formulation immediately gives the exact singleton
non-openness clause used in the frozen target `ModuliCurve`. -/
theorem not_isOpen_singleton_image
    {interval : Set ℝ} {Target : Type targetUniverse}
    [TopologicalSpace Target]
    (curve : interval → Target) (curveContinuous : Continuous curve)
    (curveInjective : Function.Injective curve) (parameter : interval)
    (parameterInterior : parameter.val ∈ interior interval) :
    ¬ IsOpen ({curve parameter} : Set Target) := by
  intro singletonOpen
  have singletonNeighborhood :
      ({curve parameter} : Set Target) ∈ nhds (curve parameter) :=
    singletonOpen.mem_nhds (mem_singleton (curve parameter))
  rcases exists_distinct_image_mem_of_mem_nhds curve curveContinuous
    curveInjective parameter parameterInterior singletonNeighborhood with
    ⟨other, _otherNe, otherImageIn, otherImageNe⟩
  exact otherImageNe (by
    simpa only [mem_singleton_iff] using otherImageIn)

end Grad.MainAssembly.ModuliCurveNonisolation
