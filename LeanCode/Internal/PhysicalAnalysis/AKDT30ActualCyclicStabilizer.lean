import AKDT29ActualCyclicFieldShift

noncomputable section
open Set

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily

/-- The lower stabilizer inclusion follows from the actual periodic fields,
with positive magnetic sign, for every listed cyclic rotation. -/
theorem actual_cyclic_rotation_stabilizes (length : ℝ) (family : CellSolutionFamily length) (period : ℕ)
    (periodPositive : 0 < period)
    (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Icc family.lower family.upper)
    (magnetic : Vec → Vec) (pressure : Vec → ℝ)
    (same : ∀ argument,
      magnetic ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).magnetic argument ∧
      pressure ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).pressure argument)
    (index : ℕ) (orthogonal : Vec ≃ₗᵢ[ℝ] Vec) (translation : Vec)
    (motion : ∀ point : Vec, orthogonal point + translation = rotation (2 * Real.pi * index / period) point) :
    SignedStabilizes (range (sampledRepresentativeFamily length family period epsilonIn potential parameter).position)
      magnetic pressure orthogonal translation := by
  let configuration := sampledRepresentativeFamily length family period epsilonIn potential parameter
  let shift := 2 * Real.pi * index / period
  have translationZero : translation = 0 := by
    have zero := motion 0
    have rotationZero : rotation (2 * Real.pi * index / period) (0 : Vec) = 0 := by
      ext coordinate
      fin_cases coordinate <;> simp [rotation, vector]
    simpa only [map_zero, zero_add, rotationZero] using zero
  subst translation
  have orthogonalSame (point : Vec) : orthogonal point = rotation shift point := by simpa only [add_zero] using motion point
  have shifted (point : ClosedDisk) (time : ℝ) :
      configuration.position (referenceCover (point, time + shift)) = rotation shift (configuration.position (referenceCover (point, time))) ∧
      configuration.magnetic (referenceCover (point, time + shift)) = rotation shift (configuration.magnetic (referenceCover (point, time))) ∧
      configuration.pressure (referenceCover (point, time + shift)) = configuration.pressure (referenceCover (point, time)) :=
    actual_reference_cyclic_shift length family period epsilonIn potential parameter periodPositive index point time
  have bodyEquality : (fun point : Vec => orthogonal point + 0) '' range configuration.position = range configuration.position := by
    apply Subset.antisymm
    · rintro point ⟨source, ⟨reference, rfl⟩, rfl⟩
      obtain ⟨argument, rfl⟩ := referenceCover_surjective reference
      refine ⟨referenceCover (argument.1, argument.2 + shift), ?_⟩
      simpa only [add_zero, orthogonalSame] using (shifted argument.1 argument.2).1
    · rintro point ⟨reference, rfl⟩
      obtain ⟨argument, rfl⟩ := referenceCover_surjective reference
      refine ⟨configuration.position (referenceCover (argument.1, argument.2 - shift)), ⟨_, rfl⟩, ?_⟩
      have relation := (shifted argument.1 (argument.2 - shift)).1
      simpa only [sub_add_cancel, add_zero, orthogonalSame] using relation.symm
  refine ⟨bodyEquality, ?_, 1, Or.inl rfl, ?_⟩
  · rintro point ⟨reference, rfl⟩
    obtain ⟨argument, rfl⟩ := referenceCover_surjective reference
    have relation := shifted argument.1 argument.2
    change pressure (orthogonal (configuration.position (referenceCover argument)) + 0) = pressure (configuration.position (referenceCover argument))
    rw [add_zero, orthogonalSame, ← relation.1,
      (same (referenceCover (argument.1, argument.2 + shift))).2, relation.2.2, (same (referenceCover argument)).2]
  · rintro point ⟨reference, rfl⟩
    obtain ⟨argument, rfl⟩ := referenceCover_surjective reference
    have relation := shifted argument.1 argument.2
    change magnetic (orthogonal (configuration.position (referenceCover argument)) + 0) = 1 • orthogonal (magnetic (configuration.position (referenceCover argument)))
    rw [add_zero, one_smul, orthogonalSame, ← relation.1,
      (same (referenceCover (argument.1, argument.2 + shift))).1, relation.2.1,
      (same (referenceCover argument)).1]
    exact (orthogonalSame _).symm

end Grad.PhysicalGeometry
