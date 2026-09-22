import RelatedEquivalence

noncomputable section

open Set

namespace Grad.MainAssembly.TargetPhysicalSimilarity

open Grad.MainTarget

/-- The exact physical comparison left after an arbitrary target reference
reparametrization has disappeared.  The physical body and distinguished axis
are transported by one positive similarity, and the reconstructed magnetic
and pressure fields obey the literal amplitude and offset laws on the body. -/
def PhysicalSimilarity (first second : Representative) (cellLength : ℝ)
    (period : ℕ) : Prop :=
  ∃ (spatialScale amplitude : ℝ) (orthogonal : Vec ≃ₗᵢ[ℝ] Vec)
    (translation : Vec) (pressureOffset : ℝ)
    (firstMagnetic secondMagnetic : Vec → Vec)
    (firstPressure secondPressure : Vec → ℝ),
    0 < spatialScale ∧ amplitude ≠ 0 ∧
    SmoothNear (Set.range first.position) firstMagnetic ∧
    SmoothNear (Set.range first.position) firstPressure ∧
    SmoothNear (Set.range second.position) secondMagnetic ∧
    SmoothNear (Set.range second.position) secondPressure ∧
    (∀ point : Reference,
      firstMagnetic (first.position point) = first.magnetic point ∧
      firstPressure (first.position point) = first.pressure point) ∧
    (∀ point : Reference,
      secondMagnetic (second.position point) = second.magnetic point ∧
      secondPressure (second.position point) = second.pressure point) ∧
    roundAxis (period * cellLength) ⊆ interior (Set.range first.position) ∧
    roundAxis (period * cellLength) ⊆ interior (Set.range second.position) ∧
    let motion := fun point : Vec =>
      spatialScale • orthogonal point + translation
    motion '' Set.range first.position = Set.range second.position ∧
    motion '' roundAxis (period * cellLength) =
      roundAxis (period * cellLength) ∧
    (∀ point ∈ Set.range first.position,
      secondMagnetic (motion point) =
        amplitude • orthogonal (firstMagnetic point)) ∧
    (∀ point ∈ Set.range first.position,
      secondPressure (motion point) =
        amplitude ^ 2 * firstPressure point + pressureOffset)

/-- Exact `NG_R16` bridge at the frozen target boundary: a full `Related`
witness, including an arbitrary reference reparametrization, induces the
physical similarity comparison for the reconstructed fields supplied by the
two literal `PhysicalConclusions` witnesses. -/
theorem physicalSimilarity_of_related
    {regularity : Regularity} (first second : Configuration regularity)
    (cellLength : ℝ) (period : ℕ)
    (firstConclusions : PhysicalConclusions first.val cellLength period)
    (secondConclusions : PhysicalConclusions second.val cellLength period)
    (related : Related regularity first second) :
    PhysicalSimilarity first.val second.val cellLength period := by
  rcases firstConclusions with
    ⟨_, firstMagnetic, firstPressure,
      firstMagneticSmooth, firstPressureSmooth, firstRepresents, _, _,
      firstAxisInterior, _, firstZeroAxis, _, _, _, _⟩
  rcases secondConclusions with
    ⟨_, secondMagnetic, secondPressure,
      secondMagneticSmooth, secondPressureSmooth, secondRepresents, _, _,
      secondAxisInterior, _, secondZeroAxis, _, _, _, _⟩
  rcases related with
    ⟨spatialScale, amplitude, orthogonal, translation, pressureOffset,
      reparametrization, scalePositive, amplitudeNonzero, _, relation⟩
  let motion := fun point : Vec =>
    spatialScale • orthogonal point + translation
  have bodyEquality :
      motion '' Set.range first.val.position = Set.range second.val.position := by
    apply Set.Subset.antisymm
    · rintro point ⟨source, ⟨parameter, rfl⟩, rfl⟩
      refine ⟨reparametrization.symm parameter, ?_⟩
      simpa [motion] using (relation (reparametrization.symm parameter)).1
    · rintro point ⟨parameter, rfl⟩
      refine ⟨first.val.position (reparametrization parameter),
        ⟨reparametrization parameter, rfl⟩, ?_⟩
      exact (relation parameter).1.symm
  have magneticEquality : ∀ point ∈ Set.range first.val.position,
      secondMagnetic (motion point) =
        amplitude • orthogonal (firstMagnetic point) := by
    rintro point ⟨parameter, rfl⟩
    calc
      secondMagnetic (motion (first.val.position parameter)) =
          secondMagnetic
            (second.val.position (reparametrization.symm parameter)) := by
        rw [(relation (reparametrization.symm parameter)).1]
        simp [motion]
      _ = second.val.magnetic (reparametrization.symm parameter) :=
        (secondRepresents (reparametrization.symm parameter)).1
      _ = amplitude • orthogonal
          (first.val.magnetic
            (reparametrization (reparametrization.symm parameter))) :=
        (relation (reparametrization.symm parameter)).2.1
      _ = amplitude • orthogonal
          (firstMagnetic (first.val.position parameter)) := by
        rw [reparametrization.apply_symm_apply]
        rw [← (firstRepresents parameter).1]
  have pressureEquality : ∀ point ∈ Set.range first.val.position,
      secondPressure (motion point) =
        amplitude ^ 2 * firstPressure point + pressureOffset := by
    rintro point ⟨parameter, rfl⟩
    calc
      secondPressure (motion (first.val.position parameter)) =
          secondPressure
            (second.val.position (reparametrization.symm parameter)) := by
        rw [(relation (reparametrization.symm parameter)).1]
        simp [motion]
      _ = second.val.pressure (reparametrization.symm parameter) :=
        (secondRepresents (reparametrization.symm parameter)).2
      _ = amplitude ^ 2 * first.val.pressure
          (reparametrization (reparametrization.symm parameter)) + pressureOffset :=
        (relation (reparametrization.symm parameter)).2.2
      _ = amplitude ^ 2 * firstPressure (first.val.position parameter) +
          pressureOffset := by
        rw [reparametrization.apply_symm_apply]
        rw [← (firstRepresents parameter).2]
  have axisEquality :
      motion '' roundAxis (period * cellLength) =
        roundAxis (period * cellLength) := by
    apply Set.Subset.antisymm
    · rintro point ⟨source, sourceInAxis, rfl⟩
      have sourceInBody : source ∈ Set.range first.val.position :=
        interior_subset (firstAxisInterior sourceInAxis)
      have imageInBody : motion source ∈ Set.range second.val.position := by
        rw [← bodyEquality]
        exact ⟨source, sourceInBody, rfl⟩
      apply (secondZeroAxis (motion source) imageInBody).mp
      rw [magneticEquality source sourceInBody]
      rw [(firstZeroAxis source sourceInBody).mpr sourceInAxis]
      simp
    · intro point pointInAxis
      have pointInSecondBody : point ∈ Set.range second.val.position :=
        interior_subset (secondAxisInterior pointInAxis)
      rw [← bodyEquality] at pointInSecondBody
      rcases pointInSecondBody with ⟨source, sourceInBody, rfl⟩
      refine ⟨source, ?_, rfl⟩
      apply (firstZeroAxis source sourceInBody).mp
      have secondZero : secondMagnetic (motion source) = 0 :=
        (secondZeroAxis (motion source)
          (by rw [← bodyEquality]; exact ⟨source, sourceInBody, rfl⟩)).mpr pointInAxis
      have scaledZero : amplitude • orthogonal (firstMagnetic source) = 0 := by
        rw [← magneticEquality source sourceInBody, secondZero]
      rcases smul_eq_zero.mp scaledZero with scalarZero | orthogonalZero
      · exact (amplitudeNonzero scalarZero).elim
      · apply orthogonal.injective
        simpa using orthogonalZero
  exact ⟨spatialScale, amplitude, orthogonal, translation, pressureOffset,
    firstMagnetic, secondMagnetic, firstPressure, secondPressure,
    scalePositive, amplitudeNonzero,
    firstMagneticSmooth, firstPressureSmooth,
    secondMagneticSmooth, secondPressureSmooth,
    firstRepresents, secondRepresents,
    firstAxisInterior, secondAxisInterior,
    bodyEquality, axisEquality, magneticEquality, pressureEquality⟩

end Grad.MainAssembly.TargetPhysicalSimilarity
