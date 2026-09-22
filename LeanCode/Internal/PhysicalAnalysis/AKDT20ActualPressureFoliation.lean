import AKDT19ActualRegularLevels

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian

variable (length : ℝ) (family : CellSolutionFamily length) (period : ℕ)
  (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
  (potential : ℝ) (parameter : Icc family.lower family.upper)
  (valid : IsConfiguration .smooth (sampledRepresentativeFamily length family period epsilonIn potential parameter))
  (injective : ∀ (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
    Function.Injective (fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val)
      (coordinateDirection point time)))

include valid injective in
theorem actual_reference_frontier_iff (reference : Reference) :
    (sampledRepresentativeFamily length family period epsilonIn potential parameter).position reference ∈
      frontier (range (sampledRepresentativeFamily length family period epsilonIn potential parameter).position) ↔ ‖reference.1.val‖ = 1 := by
  obtain ⟨argument, rfl⟩ := referenceCover_surjective reference
  exact (actual_position_interior_frontier length family period epsilonIn potential parameter valid injective argument).2

include valid injective in
theorem actual_boundary_torus_range :
    range (actualTorus length family period epsilonIn potential parameter ⟨1, zero_lt_one, le_rfl⟩) =
      frontier (range (sampledRepresentativeFamily length family period epsilonIn potential parameter).position) := by
  ext point
  constructor
  · rintro ⟨angles, rfl⟩
    exact (actual_reference_frontier_iff length family period epsilonIn potential parameter valid injective _).mpr
      (referenceTorus_norm ⟨1, zero_lt_one, le_rfl⟩ angles)
  · intro boundary
    have bodyClosed : IsClosed (range (sampledRepresentativeFamily length family period epsilonIn potential parameter).position) := by
      simpa only [image_univ] using (reference_isCompact.image valid.1.2.1.continuous).isClosed
    have bodyIn := frontier_subset_closure boundary
    rw [bodyClosed.closure_eq] at bodyIn
    obtain ⟨reference, rfl⟩ := bodyIn
    have normOne := (actual_reference_frontier_iff length family period epsilonIn potential parameter valid injective reference).mp boundary
    have inRange : reference ∈ range (referenceTorus ⟨1, zero_lt_one, le_rfl⟩) := by
      rw [referenceTorus_range]
      exact normOne
    obtain ⟨angles, rfl⟩ := inRange
    exact ⟨angles, rfl⟩

include valid injective in
/-- The literal full pressure foliation of the SAME body minus its exact
axis, with its actual smooth local extensions and radius-one frontier leaf. -/
theorem actual_pressure_foliation
    (magnetic : Vec → Vec) (pressure : Vec → ℝ)
    (magneticSmooth : ContDiff ℝ ∞ magnetic) (pressureSmooth : ContDiff ℝ ∞ pressure)
    (same : ∀ argument,
      magnetic ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).magnetic argument ∧
      pressure ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).pressure argument) :
    IsPressureFoliation (range (sampledRepresentativeFamily length family period epsilonIn potential parameter).position)
      (roundAxis ((period : ℝ) * length)) pressure := by
  have regular := (actual_regular_pressure_levels length family period epsilonIn potential parameter valid injective
    magnetic pressure magneticSmooth pressureSmooth same).1
  refine ⟨actualFoliation length family period epsilonIn potential parameter,
    actualFoliation_local_extensions length family period epsilonIn potential parameter,
    actualFoliation_isEmbedding length family period epsilonIn potential parameter valid,
    actualFoliation_range length family period epsilonIn potential parameter valid,
    actualFoliation_derivative_injective length family period epsilonIn potential parameter injective, ?_, ?_⟩
  · intro radius
    exact ⟨potential - radius.val ^ 2, regular radius,
      actual_pressure_level_range length family period epsilonIn potential parameter pressure (fun argument => (same argument).2) radius⟩
  · exact actual_boundary_torus_range length family period epsilonIn potential parameter valid injective

end Grad.PhysicalGeometry
