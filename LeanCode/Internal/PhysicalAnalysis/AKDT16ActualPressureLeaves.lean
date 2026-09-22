import AKDT15ActualFoliationSmoothness

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledConfigurationRegularity

variable (length : ℝ) (family : CellSolutionFamily length) (period : ℕ)
  (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
  (potential : ℝ) (parameter : Icc family.lower family.upper)
  (valid : IsConfiguration .smooth (sampledRepresentativeFamily length family period epsilonIn potential parameter))

include valid in
theorem actual_reference_axis_iff (reference : Reference) :
    (sampledRepresentativeFamily length family period epsilonIn potential parameter).position reference ∈ roundAxis ((period : ℝ) * length) ↔
      reference.1.val = 0 := by
  obtain ⟨argument, rfl⟩ := referenceCover_surjective reference
  exact actual_position_mem_axis_iff length family period epsilonIn potential parameter valid argument

include valid in
theorem actualFoliation_isEmbedding :
    Topology.IsEmbedding (actualFoliation length family period epsilonIn potential parameter) :=
  valid.1.2.1.comp referenceFoliation_isEmbedding

include valid in
theorem actualFoliation_range :
    range (actualFoliation length family period epsilonIn potential parameter) =
      range (sampledRepresentativeFamily length family period epsilonIn potential parameter).position \ roundAxis ((period : ℝ) * length) := by
  ext point
  constructor
  · rintro ⟨argument, rfl⟩
    refine ⟨⟨referenceFoliation argument, rfl⟩, ?_⟩
    change (sampledRepresentativeFamily length family period epsilonIn potential parameter).position (referenceFoliation argument) ∉ _
    rw [actual_reference_axis_iff length family period epsilonIn potential parameter valid]
    exact (polarDiskPoint (argument.1, argument.2.1)).property
  · rintro ⟨⟨reference, rfl⟩, outside⟩
    have nonzero : reference.1.val ≠ 0 := by
      rwa [actual_reference_axis_iff length family period epsilonIn potential parameter valid] at outside
    have inRange : reference ∈ range referenceFoliation := by rwa [referenceFoliation_range]
    obtain ⟨argument, rfl⟩ := inRange
    exact ⟨argument, rfl⟩

variable (pressure : Vec → ℝ)
  (same : ∀ argument,
    pressure ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
      (sampledRepresentativeFamily length family period epsilonIn potential parameter).pressure argument)

include same in
theorem actual_pressure_reference (reference : Reference) :
    pressure ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position reference) = potential - ‖reference.1.val‖ ^ 2 := by
  obtain ⟨argument, rfl⟩ := referenceCover_surjective reference
  rw [same, ← (sampled_actual_lifts_values length family period epsilonIn potential parameter argument).2.2]
  simp [sampledPressureCoordinateValue, sampledPressureLift, referenceCoverPoint, referenceCover]

include same in
theorem actual_pressure_torus (radius : Ioc (0 : ℝ) 1) (angles : Torus) :
    pressure ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position (referenceTorus radius angles)) =
      potential - radius.val ^ 2 := by
  rw [actual_pressure_reference length family period epsilonIn potential parameter pressure same, referenceTorus_norm]

include same in
/-- Each nonzero radius gives exactly its actual pressure level, including the
outermost r=1 level. -/
theorem actual_pressure_level_range (radius : Ioc (0 : ℝ) 1) :
    range ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position ∘ referenceTorus radius) =
      pressureLevel (range (sampledRepresentativeFamily length family period epsilonIn potential parameter).position)
        pressure (potential - radius.val ^ 2) := by
  ext point
  constructor
  · rintro ⟨angles, rfl⟩
    exact ⟨⟨referenceTorus radius angles, rfl⟩,
      actual_pressure_torus length family period epsilonIn potential parameter pressure same radius angles⟩
  · rintro ⟨⟨reference, rfl⟩, value⟩
    rw [actual_pressure_reference length family period epsilonIn potential parameter pressure same] at value
    have normSame : ‖reference.1.val‖ = radius.val := by nlinarith [norm_nonneg reference.1.val, radius.property.1]
    have inRange : reference ∈ range (referenceTorus radius) := by rwa [referenceTorus_range]
    obtain ⟨angles, rfl⟩ := inRange
    exact ⟨angles, rfl⟩

end Grad.PhysicalGeometry
