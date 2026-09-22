import QT3StateDensity

noncomputable section

namespace Grad.RealFixedRanges

section Copy

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A grade-tagged copy of the literal smooth core. Its tag is its actual
injective embedding, so distinct grade norms are not installed on one core. -/
structure NormedCoreCopy (embedding : E →ₗ[ℝ] F) (injective : Function.Injective embedding) where
  toCore : E

namespace NormedCoreCopy

variable {embedding : E →ₗ[ℝ] F} {injective : Function.Injective embedding}

@[ext] theorem ext {first second : NormedCoreCopy embedding injective}
    (equality : first.toCore = second.toCore) : first = second := by
  cases first
  cases second
  cases equality
  rfl

theorem toCore_injective : Function.Injective
    (toCore : NormedCoreCopy embedding injective → E) := fun _ _ equality => ext equality

instance : Zero (NormedCoreCopy embedding injective) := ⟨⟨0⟩⟩
instance : Add (NormedCoreCopy embedding injective) := ⟨fun first second => ⟨first.toCore + second.toCore⟩⟩
instance : Neg (NormedCoreCopy embedding injective) := ⟨fun field => ⟨-field.toCore⟩⟩
instance : Sub (NormedCoreCopy embedding injective) := ⟨fun first second => ⟨first.toCore - second.toCore⟩⟩
instance : SMul ℕ (NormedCoreCopy embedding injective) := ⟨fun scalar field => ⟨scalar • field.toCore⟩⟩
instance : SMul ℤ (NormedCoreCopy embedding injective) := ⟨fun scalar field => ⟨scalar • field.toCore⟩⟩
instance : SMul ℝ (NormedCoreCopy embedding injective) := ⟨fun scalar field => ⟨scalar • field.toCore⟩⟩

instance : AddCommGroup (NormedCoreCopy embedding injective) :=
  toCore_injective.addCommGroup toCore rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

def toCoreAddHom : NormedCoreCopy embedding injective →+ E where
  toFun := toCore
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module ℝ (NormedCoreCopy embedding injective) :=
  Function.Injective.module ℝ toCoreAddHom toCore_injective (fun _ _ => rfl)

def toCoreLinear : NormedCoreCopy embedding injective →ₗ[ℝ] E where
  toFun := toCore
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def ofCore (embedding : E →ₗ[ℝ] F) (injective : Function.Injective embedding) :
    E →ₗ[ℝ] NormedCoreCopy embedding injective where
  toFun := fun field => ⟨field⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def toAmbient (embedding : E →ₗ[ℝ] F) (injective : Function.Injective embedding) :
    NormedCoreCopy embedding injective →ₗ[ℝ] F := embedding.comp toCoreLinear

theorem toAmbient_injective : Function.Injective (toAmbient embedding injective) :=
  injective.comp toCore_injective

instance : NormedAddCommGroup (NormedCoreCopy embedding injective) :=
  NormedAddCommGroup.induced _ _ (toAmbient embedding injective) toAmbient_injective

instance : NormedSpace ℝ (NormedCoreCopy embedding injective) :=
  NormedSpace.induced ℝ _ _ (toAmbient embedding injective)

def isometricEmbedding (embedding : E →ₗ[ℝ] F) (injective : Function.Injective embedding) :
    NormedCoreCopy embedding injective →ₗᵢ[ℝ] F :=
  { toAmbient embedding injective with norm_map' := fun _ => rfl }

theorem norm_eq (field : NormedCoreCopy embedding injective) :
    ‖field‖ = ‖embedding field.toCore‖ := rfl

theorem isometricEmbedding_denseRange (dense : DenseRange embedding) :
    DenseRange (isometricEmbedding embedding injective) := by
  apply dense.mono
  rintro _ ⟨field, rfl⟩
  exact ⟨⟨field⟩, rfl⟩

end NormedCoreCopy
end Copy

open Grad.CartesianState Grad.Constraints

abbrev StateGradeCore (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :=
  NormedCoreCopy (E := stateSmoothRange parameters parameter inside)
    (F := stateRange parameters parameter inside grade large)
    (stateSmoothEmbedding parameters parameter inside grade large)
    (stateSmoothEmbedding_injective parameters parameter inside grade large)

abbrev SourceGradeCore (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :=
  NormedCoreCopy (E := sourceSmoothRange parameters) (F := sourceRange parameters grade large)
    (sourceSmoothEmbedding parameters grade large)
    (sourceSmoothEmbedding_injective parameters grade large)

end Grad.RealFixedRanges
