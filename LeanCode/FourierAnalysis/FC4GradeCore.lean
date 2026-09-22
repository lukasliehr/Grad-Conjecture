import FC3Proof

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators Topology

namespace Grad.CartesianState

open Grad.ClosedJets

/-- A grade-tagged copy of the one all-grade core.  The tag prevents distinct
M2 seminorms from being installed on the untagged `ACore`. -/
structure GradeCore (parameters : PhaseParameters) (dimension grade : ℕ) where
  toCore : ACore parameters dimension

namespace GradeCore

variable {parameters : PhaseParameters} {dimension grade : ℕ}

@[ext]
theorem ext {first second : GradeCore parameters dimension grade}
    (equality : first.toCore = second.toCore) : first = second := by
  cases first
  cases second
  cases equality
  rfl

theorem toCore_injective :
    Function.Injective (toCore : GradeCore parameters dimension grade → ACore parameters dimension) := by
  intro first second equality
  exact ext equality

instance : Zero (GradeCore parameters dimension grade) := ⟨⟨0⟩⟩
instance : Add (GradeCore parameters dimension grade) :=
  ⟨fun first second => ⟨first.toCore + second.toCore⟩⟩
instance : Neg (GradeCore parameters dimension grade) :=
  ⟨fun field => ⟨-field.toCore⟩⟩
instance : Sub (GradeCore parameters dimension grade) :=
  ⟨fun first second => ⟨first.toCore - second.toCore⟩⟩
instance : SMul ℕ (GradeCore parameters dimension grade) :=
  ⟨fun scalar field => ⟨scalar • field.toCore⟩⟩
instance : SMul ℤ (GradeCore parameters dimension grade) :=
  ⟨fun scalar field => ⟨scalar • field.toCore⟩⟩
instance : SMul ℂ (GradeCore parameters dimension grade) :=
  ⟨fun scalar field => ⟨scalar • field.toCore⟩⟩

instance : AddCommGroup (GradeCore parameters dimension grade) :=
  toCore_injective.addCommGroup toCore rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

def toCoreAddHom : GradeCore parameters dimension grade →+ ACore parameters dimension where
  toFun := toCore
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module ℂ (GradeCore parameters dimension grade) :=
  Function.Injective.module ℂ toCoreAddHom toCore_injective (fun _ _ => rfl)

def toCoreLinear : GradeCore parameters dimension grade →ₗ[ℂ] ACore parameters dimension where
  toFun := toCore
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def ofCoreLinear : ACore parameters dimension →ₗ[ℂ] GradeCore parameters dimension grade where
  toFun field := ⟨field⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ofCore_toCore (field : GradeCore parameters dimension grade) :
    ofCoreLinear field.toCore = field := by
  exact ext rfl

theorem toCore_ofCore (field : ACore parameters dimension) :
    (ofCoreLinear (grade := grade) field).toCore = field := rfl

end GradeCore

/-- COR03 coordinates, now with the grade represented in the source type. -/
def gradeCoreCoordinates {dimension grade : ℕ} (parameters : PhaseParameters) :
    GradeCore parameters dimension grade →ₗ[ℂ]
      lp (fun _ : ℤ => CartesianGradeRow dimension grade) 2 :=
  (cartesianGradeCoordinates parameters grade).comp GradeCore.toCoreLinear

theorem gradeCoreCoordinates_apply {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension grade) :
    gradeCoreCoordinates parameters field =
      cartesianGradeCoordinates parameters grade field.toCore := rfl

/-- The literal pullback of the coordinate Hilbert inner product. -/
def cartesianGradeInner {dimension grade : ℕ} (parameters : PhaseParameters)
    (first second : GradeCore parameters dimension grade) : ℂ :=
  inner ℂ (gradeCoreCoordinates parameters first) (gradeCoreCoordinates parameters second)

/-- The bundled positive-semidefinite inner-product laws inherited from the coordinate Hilbert space. -/
@[instance_reducible]
def cartesianGradePreInnerCore {dimension grade : ℕ} (parameters : PhaseParameters) :
    PreInnerProductSpace.Core ℂ (GradeCore parameters dimension grade) where
  inner := cartesianGradeInner parameters
  conj_inner_symm first second := by
    exact inner_conj_symm _ _
  re_inner_nonneg field := by
    unfold cartesianGradeInner
    exact inner_self_nonneg
  add_left first second third := by
    unfold cartesianGradeInner
    rw [map_add, inner_add_left]
  smul_left first second scalar := by
    unfold cartesianGradeInner
    rw [map_smul, inner_smul_left]

/-- The literal M2 seminorm, pulled back from the coordinate Hilbert norm. -/
def cartesianGradeSeminorm {dimension grade : ℕ} (parameters : PhaseParameters) :
    Seminorm ℂ (GradeCore parameters dimension grade) :=
  (normSeminorm ℂ
    (lp (fun _ : ℤ => CartesianGradeRow dimension grade) 2)).comp
      (gradeCoreCoordinates parameters)

theorem cartesianGradeSeminorm_apply {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension grade) :
    cartesianGradeSeminorm parameters field =
      ‖gradeCoreCoordinates parameters field‖ := rfl

theorem cartesianGradeInner_self {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension grade) :
    Complex.re (cartesianGradeInner parameters field field) =
      cartesianGradeSeminorm parameters field ^ 2 := by
  rw [cartesianGradeSeminorm_apply]
  change Complex.re (inner ℂ (gradeCoreCoordinates parameters field)
    (gradeCoreCoordinates parameters field)) = _
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem cartesianGradeSeminorm_triangle {dimension grade : ℕ}
    (parameters : PhaseParameters) (first second : GradeCore parameters dimension grade) :
    cartesianGradeSeminorm parameters (first + second) ≤
      cartesianGradeSeminorm parameters first + cartesianGradeSeminorm parameters second :=
  map_add_le_add (cartesianGradeSeminorm parameters) first second

theorem cartesianGradeSeminorm_smul {dimension grade : ℕ}
    (parameters : PhaseParameters) (scalar : ℂ)
    (field : GradeCore parameters dimension grade) :
    cartesianGradeSeminorm parameters (scalar • field) =
      ‖scalar‖ * cartesianGradeSeminorm parameters field :=
  map_smul_eq_mul (cartesianGradeSeminorm parameters) scalar field

theorem cartesianGradeSeminorm_sq {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension grade) :
    cartesianGradeSeminorm parameters field ^ 2 =
      ∑' cell : ℤ, ∑ index : GradeMultiIndex grade,
        cellFrequency cell ^ (2 * (grade - cartesianOrder index.toCartesian)) *
          ∫ point : SpatialPlane,
            ‖closedDiskLift
              (closedMultiDerivative
                (phaseWeightedJet parameters cell (field.toCore.1 cell))
                index.toCartesian) point‖ ^ 2
              ∂volume.restrict openUnitDisk := by
  rw [cartesianGradeSeminorm_apply, gradeCoreCoordinates_apply]
  exact cartesianGradeCoordinates_norm_sq_expanded parameters grade field.toCore

end Grad.CartesianState
