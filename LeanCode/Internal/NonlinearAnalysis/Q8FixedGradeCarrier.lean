import Q8FixedGradeWeights
import Mathlib.Analysis.Normed.Module.Completion

noncomputable section

open scoped BigOperators

namespace Grad.Q8FixedGrade

open Grad.CartesianState Grad.NonlinearQuotientBounds

/-- A grade tag keeps the distinct literal envelope norms on distinct types. -/
structure Core (parameters : PhaseParameters) (grade : ℕ) where
  toCore : TameCoefficient parameters

def coreEquiv (parameters : PhaseParameters) (grade : ℕ) :
    Core parameters grade ≃ TameCoefficient parameters where
  toFun := Core.toCore
  invFun := Core.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance {parameters : PhaseParameters} {grade : ℕ} : CommRing (Core parameters grade) :=
  (coreEquiv parameters grade).commRing

instance {parameters : PhaseParameters} {grade : ℕ} : Module ℂ (Core parameters grade) :=
  (coreEquiv parameters grade).module ℂ

/-- The envelope is definite on the literal coefficient core. -/
theorem envelope_eq_zero {parameters : PhaseParameters} (grade : ℕ)
    (value : TameCoefficient parameters) (zeroNorm : coefficientEnvelope grade value = 0) :
    value = 0 := by
  apply Subtype.ext
  funext cell
  apply norm_eq_zero.mp
  have bound := norm_le_tameEnvelope value.property grade cell
  change ‖value.val cell‖ ≤ coefficientEnvelope grade value at bound
  rw [zeroNorm] at bound
  exact le_antisymm bound (norm_nonneg _)

/-- The original, unscaled Q8 envelope as a norm on the grade-tagged core. -/
def coreNorm (parameters : PhaseParameters) (grade : ℕ) :
    AddGroupNorm (Core parameters grade) where
  toFun value := coefficientEnvelope grade value.toCore
  map_zero' := by
    change coefficientEnvelope grade (0 : TameCoefficient parameters) = 0
    simp [coefficientEnvelope, tameEnvelope, tameEnvelopeTerm]
  add_le' first second := coefficientEnvelope_add_le grade first.toCore second.toCore
  neg' value := coefficientEnvelope_neg grade value.toCore
  eq_zero_of_map_eq_zero' value zeroNorm :=
    (coreEquiv parameters grade).injective (envelope_eq_zero grade value.toCore zeroNorm)

instance {parameters : PhaseParameters} {grade : ℕ} : NormedCommRing (Core parameters grade) where
  __ := (coreNorm parameters grade).toNormedAddCommGroup
  __ : CommRing (Core parameters grade) := inferInstance
  norm_mul_le first second := envelope_mul_le parameters grade first.toCore second.toCore

theorem core_norm {parameters : PhaseParameters} {grade : ℕ} (value : Core parameters grade) :
    ‖value‖ = coefficientEnvelope grade value.toCore := rfl

instance {parameters : PhaseParameters} {grade : ℕ} : NormedSpace ℂ (Core parameters grade) where
  norm_smul_le scalar value := (coefficientEnvelope_smul grade scalar value.toCore).le

instance {parameters : PhaseParameters} {grade : ℕ} : Algebra ℂ (Core parameters grade) :=
  Algebra.ofModule
    (fun scalar first second => (coreEquiv parameters grade).injective
      (tameSmul_mul scalar first.toCore second.toCore))
    (fun scalar first second => (coreEquiv parameters grade).injective
      (tameMul_smul scalar first.toCore second.toCore))

instance {parameters : PhaseParameters} {grade : ℕ} : NormedAlgebra ℂ (Core parameters grade) where
  norm_smul_le := norm_smul_le

instance {parameters : PhaseParameters} {grade : ℕ} : NormedSpace ℝ (Core parameters grade) :=
  NormedSpace.restrictScalars ℝ ℂ (Core parameters grade)

/-- Completion in the exact Q8 envelope, retaining the original width and grade. -/
abbrev Carrier (parameters : PhaseParameters) (grade : ℕ) :=
  UniformSpace.Completion (Core parameters grade)

def coreLinear (parameters : PhaseParameters) (grade : ℕ) :
    TameCoefficient parameters →ₗ[ℂ] Core parameters grade where
  toFun := Core.mk
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The literal all-grade coefficients included into a fixed-grade completion. -/
def embed (parameters : PhaseParameters) (grade : ℕ) :
    TameCoefficient parameters →ₗ[ℂ] Carrier parameters grade :=
  ((UniformSpace.Completion.toComplₗᵢ : Core parameters grade →ₗᵢ[ℂ]
    Carrier parameters grade).toLinearMap).comp (coreLinear parameters grade)

theorem embed_norm (parameters : PhaseParameters) (grade : ℕ)
    (value : TameCoefficient parameters) :
    ‖embed parameters grade value‖ = coefficientEnvelope grade value :=
  UniformSpace.Completion.norm_coe (Core.mk value : Core parameters grade)

theorem embed_injective (parameters : PhaseParameters) (grade : ℕ) :
    Function.Injective (embed parameters grade) := by
  intro first second equality
  apply sub_eq_zero.mp
  apply envelope_eq_zero grade
  rw [← embed_norm, map_sub, equality, sub_self, norm_zero]

theorem embed_denseRange (parameters : PhaseParameters) (grade : ℕ) :
    DenseRange (embed parameters grade) := by
  have dense : DenseRange (UniformSpace.Completion.coe' :
      Core parameters grade → Carrier parameters grade) :=
    UniformSpace.Completion.denseRange_coe
  have rangeEq : Set.range (embed parameters grade) = Set.range
      (UniformSpace.Completion.coe' : Core parameters grade → Carrier parameters grade) := by
    ext point
    constructor
    · rintro ⟨value, rfl⟩
      exact ⟨Core.mk value, rfl⟩
    · rintro ⟨value, rfl⟩
      exact ⟨value.toCore, rfl⟩
  change Dense (Set.range (embed parameters grade))
  rw [rangeEq]
  exact dense

theorem embed_mul (parameters : PhaseParameters) (grade : ℕ)
    (first second : TameCoefficient parameters) :
    embed parameters grade (first * second) =
      embed parameters grade first * embed parameters grade second :=
  UniformSpace.Completion.coe_mul (Core.mk first : Core parameters grade) (Core.mk second)

theorem embed_one (parameters : PhaseParameters) (grade : ℕ) :
    embed parameters grade 1 = 1 := UniformSpace.Completion.coe_one (Core parameters grade)

theorem embed_pow (parameters : PhaseParameters) (grade power : ℕ)
    (value : TameCoefficient parameters) :
    embed parameters grade (value ^ power) = (embed parameters grade value) ^ power := by
  induction power with
  | zero => simp only [pow_zero, embed_one]
  | succ power hypothesis => rw [pow_succ, embed_mul, hypothesis, pow_succ]

end Grad.Q8FixedGrade
