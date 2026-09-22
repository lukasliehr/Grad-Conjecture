import QU6Consumer

noncomputable section

namespace Grad.ConstrainedGrades

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges

abbrev AdmissibleGrade := {grade : ℕ // 3 ≤ grade}

/-- Actual dependent real constrained state families, with the canonical
coefficient-inclusion equations at every pair of grades q >= 3. -/
def compatibleStateSubmodule (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    Submodule ℝ (∀ grade : AdmissibleGrade, stateRange parameters parameter inside grade.val grade.property) where
  carrier family := ∀ lower upper : AdmissibleGrade, ∀ ordered : lower.val ≤ upper.val,
    stateLowering parameters parameter inside lower.property ordered (family upper) = family lower
  zero_mem' := by
    intro lower upper ordered
    exact (stateLowering parameters parameter inside lower.property ordered).map_zero
  add_mem' := by
    intro first second firstCompatible secondCompatible lower upper ordered
    change stateLowering parameters parameter inside lower.property ordered (first upper + second upper) = _
    rw [map_add, firstCompatible lower upper ordered, secondCompatible lower upper ordered]
    rfl
  smul_mem' := by
    intro scalar family compatible lower upper ordered
    change stateLowering parameters parameter inside lower.property ordered (scalar • family upper) = _
    rw [map_smul, compatible lower upper ordered]
    rfl

def compatibleSourceSubmodule (parameters : PhaseParameters) :
    Submodule ℝ (∀ grade : AdmissibleGrade, sourceRange parameters grade.val grade.property) where
  carrier family := ∀ lower upper : AdmissibleGrade, ∀ ordered : lower.val ≤ upper.val,
    sourceLowering parameters lower.property ordered (family upper) = family lower
  zero_mem' := by
    intro lower upper ordered
    exact (sourceLowering parameters lower.property ordered).map_zero
  add_mem' := by
    intro first second firstCompatible secondCompatible lower upper ordered
    change sourceLowering parameters lower.property ordered (first upper + second upper) = _
    rw [map_add, firstCompatible lower upper ordered, secondCompatible lower upper ordered]
    rfl
  smul_mem' := by
    intro scalar family compatible lower upper ordered
    change sourceLowering parameters lower.property ordered (scalar • family upper) = _
    rw [map_smul, compatible lower upper ordered]
    rfl

abbrev CompatibleStates (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) := compatibleStateSubmodule parameters parameter inside

abbrev CompatibleSources (parameters : PhaseParameters) := compatibleSourceSubmodule parameters

def stateToCompatible (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    stateSmoothRange parameters parameter inside →ₗ[ℝ] CompatibleStates parameters parameter inside where
  toFun field := ⟨fun grade => stateSmoothEmbedding parameters parameter inside grade.val grade.property field, by
    intro lower upper ordered
    exact smoothState_compatible_family parameters parameter inside field lower.val upper.val lower.property ordered⟩
  map_add' first second := by
    apply Subtype.ext
    funext grade
    exact (stateSmoothEmbedding parameters parameter inside grade.val grade.property).map_add first second
  map_smul' scalar field := by
    apply Subtype.ext
    funext grade
    exact (stateSmoothEmbedding parameters parameter inside grade.val grade.property).map_smul scalar field

def sourceToCompatible (parameters : PhaseParameters) :
    sourceSmoothRange parameters →ₗ[ℝ] CompatibleSources parameters where
  toFun field := ⟨fun grade => sourceSmoothEmbedding parameters grade.val grade.property field, by
    intro lower upper ordered
    exact smoothSource_compatible_family parameters field lower.val upper.val lower.property ordered⟩
  map_add' first second := by
    apply Subtype.ext
    funext grade
    exact (sourceSmoothEmbedding parameters grade.val grade.property).map_add first second
  map_smul' scalar field := by
    apply Subtype.ext
    funext grade
    exact (sourceSmoothEmbedding parameters grade.val grade.property).map_smul scalar field

def compatibleStateCoordinate (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : AdmissibleGrade) :
    CompatibleStates parameters parameter inside →L[ℝ] stateRange parameters parameter inside grade.val grade.property :=
  (ContinuousLinearMap.proj grade).comp (compatibleStateSubmodule parameters parameter inside).subtypeL

def compatibleSourceCoordinate (parameters : PhaseParameters) (grade : AdmissibleGrade) :
    CompatibleSources parameters →L[ℝ] sourceRange parameters grade.val grade.property :=
  (ContinuousLinearMap.proj grade).comp (compatibleSourceSubmodule parameters).subtypeL

theorem stateToCompatible_injective (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) : Function.Injective (stateToCompatible parameters parameter inside) := by
  intro first second equal
  exact stateSmoothEmbedding_injective parameters parameter inside 3 (le_refl 3)
    (congrArg (fun family : CompatibleStates parameters parameter inside => family.val ⟨3, le_refl 3⟩) equal)

theorem sourceToCompatible_injective (parameters : PhaseParameters) : Function.Injective (sourceToCompatible parameters) := by
  intro first second equal
  exact sourceSmoothEmbedding_injective parameters 3 (le_refl 3)
    (congrArg (fun family : CompatibleSources parameters => family.val ⟨3, le_refl 3⟩) equal)

end Grad.ConstrainedGrades
