import QV1CompatibleFamilies

noncomputable section

namespace Grad.ConstrainedGrades

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.SmoothingFamily Grad.AxisCore

/-- Fill the omitted grades 0,1,2 by the actual inclusion from grade 3.
No new constrained low-grade projection is introduced. -/
def extendedState (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (family : CompatibleStates parameters parameter inside)
    (grade : ℕ) : XAmbient parameters grade :=
  xLowering parameters (le_max_left grade 3) (family.val ⟨max grade 3, le_max_right grade 3⟩).val

def extendedSource (parameters : PhaseParameters) (family : CompatibleSources parameters)
    (grade : ℕ) : ZAmbient parameters grade :=
  zLowering parameters (le_max_left grade 3) (family.val ⟨max grade 3, le_max_right grade 3⟩).val

theorem extendedState_compatible (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (family : CompatibleStates parameters parameter inside)
    (lower upper : ℕ) (ordered : lower ≤ upper) :
    xLowering parameters ordered (extendedState parameters parameter inside family upper) =
      extendedState parameters parameter inside family lower := by
  have compatible : xLowering parameters (max_le_max ordered (le_refl 3))
      (family.val ⟨max upper 3, le_max_right upper 3⟩).val =
        (family.val ⟨max lower 3, le_max_right lower 3⟩).val :=
    congrArg Subtype.val (family.property
      ⟨max lower 3, le_max_right lower 3⟩ ⟨max upper 3, le_max_right upper 3⟩ (max_le_max ordered (le_refl 3)))
  change xLowering parameters ordered
    (xLowering parameters (le_max_left upper 3) (family.val ⟨max upper 3, le_max_right upper 3⟩).val) = _
  rw [xLowering_trans]
  calc
    _ = xLowering parameters (le_max_left lower 3)
        (xLowering parameters (max_le_max ordered (le_refl 3))
          (family.val ⟨max upper 3, le_max_right upper 3⟩).val) := (xLowering_trans _ _ _ _).symm
    _ = extendedState parameters parameter inside family lower := by rw [compatible]; rfl

theorem extendedSource_compatible (parameters : PhaseParameters) (family : CompatibleSources parameters)
    (lower upper : ℕ) (ordered : lower ≤ upper) :
    zLowering parameters ordered (extendedSource parameters family upper) = extendedSource parameters family lower := by
  have compatible : zLowering parameters (max_le_max ordered (le_refl 3))
      (family.val ⟨max upper 3, le_max_right upper 3⟩).val =
        (family.val ⟨max lower 3, le_max_right lower 3⟩).val :=
    congrArg Subtype.val (family.property
      ⟨max lower 3, le_max_right lower 3⟩ ⟨max upper 3, le_max_right upper 3⟩ (max_le_max ordered (le_refl 3)))
  change zLowering parameters ordered
    (zLowering parameters (le_max_left upper 3) (family.val ⟨max upper 3, le_max_right upper 3⟩).val) = _
  rw [zLowering_trans]
  calc
    _ = zLowering parameters (le_max_left lower 3)
        (zLowering parameters (max_le_max ordered (le_refl 3))
          (family.val ⟨max upper 3, le_max_right upper 3⟩).val) := (zLowering_trans _ _ _ _).symm
    _ = extendedSource parameters family lower := by rw [compatible]; rfl

theorem extendedState_at (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (family : CompatibleStates parameters parameter inside)
    (grade : AdmissibleGrade) : extendedState parameters parameter inside family grade.val = (family.val grade).val := by
  exact congrArg Subtype.val (family.property grade
    ⟨max grade.val 3, le_max_right grade.val 3⟩ (le_max_left grade.val 3))

theorem extendedSource_at (parameters : PhaseParameters) (family : CompatibleSources parameters)
    (grade : AdmissibleGrade) : extendedSource parameters family grade.val = (family.val grade).val := by
  exact congrArg Subtype.val (family.property grade
    ⟨max grade.val 3, le_max_right grade.val 3⟩ (le_max_left grade.val 3))

theorem extendedState_core (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : stateSmoothRange parameters parameter inside) (grade : ℕ) :
    extendedState parameters parameter inside (stateToCompatible parameters parameter inside field) grade =
      stateToGrade parameters grade field.val := xLowering_core parameters (le_max_left grade 3) field.val

theorem extendedSource_core (parameters : PhaseParameters) (field : sourceSmoothRange parameters) (grade : ℕ) :
    extendedSource parameters (sourceToCompatible parameters field) grade =
      Grad.QuotientProjection.quotientEta parameters grade field.val :=
  zLowering_core parameters (le_max_left grade 3) field.val

end Grad.ConstrainedGrades
