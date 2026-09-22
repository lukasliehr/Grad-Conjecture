import QuotientDiagonal
import QuotientDeterminant

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

variable {parameters : PhaseParameters}

/-- Evaluation of complex-linear maps at one fixed point, as a linear map. -/
def linearEvaluation {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (point : M) : (M →ₗ[ℂ] N) →ₗ[ℂ] N where
  toFun mapping := mapping point
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Postcomposition of a curried trilinear tower by a linear map. -/
def trilinearPost {M₁ M₂ M₃ N N' : Type*} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
    [AddCommGroup N] [Module ℂ N] [AddCommGroup N'] [Module ℂ N']
    (tower : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃ →ₗ[ℂ] N) (post : N →ₗ[ℂ] N') :
    M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃ →ₗ[ℂ] N' where
  toFun first := (tower first).compr₂ post
  map_add' first second := by
    apply LinearMap.ext
    intro middle
    apply LinearMap.ext
    intro last
    simp only [map_add, LinearMap.compr₂_apply, LinearMap.add_apply]
  map_smul' scalar first := by
    apply LinearMap.ext
    intro middle
    apply LinearMap.ext
    intro last
    simp only [map_smul, LinearMap.compr₂_apply, LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem trilinearPost_apply {M₁ M₂ M₃ N N' : Type*} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
    [AddCommGroup N] [Module ℂ N] [AddCommGroup N'] [Module ℂ N']
    (tower : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃ →ₗ[ℂ] N) (post : N →ₗ[ℂ] N')
    (first : M₁) (middle : M₂) (last : M₃) :
    trilinearPost tower post first middle last = post (tower first middle last) := rfl

/-- A one-slot multilinear term from a linear map on the state. -/
def stateLinearMultilinear (mapping : QuotientState parameters →ₗ[ℂ] ACore parameters 1) :
    MultilinearMap ℂ (fun _ : Fin 1 => QuotientState parameters) (ACore parameters 1) :=
  MultilinearMap.ofSubsingleton ℂ (QuotientState parameters) (ACore parameters 1) (0 : Fin 1)
    mapping

@[simp] theorem stateLinearMultilinear_apply
    (mapping : QuotientState parameters →ₗ[ℂ] ACore parameters 1)
    (arguments : Fin 1 → QuotientState parameters) :
    stateLinearMultilinear mapping arguments = mapping (arguments 0) := rfl

/-- A two-slot multilinear term from a curried bilinear operation and two
linear slot maps. -/
def stateBilinearMultilinear {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    (operation : V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] ACore parameters 1)
    (firstMap : QuotientState parameters →ₗ[ℂ] V₁)
    (secondMap : QuotientState parameters →ₗ[ℂ] V₂) :
    MultilinearMap ℂ (fun _ : Fin 2 => QuotientState parameters) (ACore parameters 1) where
  toFun arguments := operation (firstMap (arguments 0)) (secondMap (arguments 1))
  map_update_add' := by
    intro _ arguments slot first second
    fin_cases slot <;> simp only [Function.update_apply] <;>
      simp [map_add, LinearMap.add_apply]
  map_update_smul' := by
    intro _ arguments slot scalar argument
    fin_cases slot <;> simp only [Function.update_apply] <;>
      simp [map_smul, LinearMap.smul_apply]

@[simp] theorem stateBilinearMultilinear_apply {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    (operation : V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] ACore parameters 1)
    (firstMap : QuotientState parameters →ₗ[ℂ] V₁)
    (secondMap : QuotientState parameters →ₗ[ℂ] V₂)
    (arguments : Fin 2 → QuotientState parameters) :
    stateBilinearMultilinear operation firstMap secondMap arguments =
      operation (firstMap (arguments 0)) (secondMap (arguments 1)) := rfl

/-- A three-slot multilinear term from a curried trilinear operation and
three linear slot maps. -/
def stateTrilinearMultilinear {V₁ V₂ V₃ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]
    (operation : V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] V₃ →ₗ[ℂ] ACore parameters 1)
    (firstMap : QuotientState parameters →ₗ[ℂ] V₁)
    (secondMap : QuotientState parameters →ₗ[ℂ] V₂)
    (thirdMap : QuotientState parameters →ₗ[ℂ] V₃) :
    MultilinearMap ℂ (fun _ : Fin 3 => QuotientState parameters) (ACore parameters 1) where
  toFun arguments :=
    operation (firstMap (arguments 0)) (secondMap (arguments 1)) (thirdMap (arguments 2))
  map_update_add' := by
    intro _ arguments slot first second
    fin_cases slot <;> simp only [Function.update_apply] <;>
      simp [Fin.ext_iff, map_add, LinearMap.add_apply]
  map_update_smul' := by
    intro _ arguments slot scalar argument
    fin_cases slot <;> simp only [Function.update_apply] <;>
      simp [Fin.ext_iff, map_smul, LinearMap.smul_apply]

@[simp] theorem stateTrilinearMultilinear_apply {V₁ V₂ V₃ : Type*} [AddCommGroup V₁]
    [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]
    (operation : V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] V₃ →ₗ[ℂ] ACore parameters 1)
    (firstMap : QuotientState parameters →ₗ[ℂ] V₁)
    (secondMap : QuotientState parameters →ₗ[ℂ] V₂)
    (thirdMap : QuotientState parameters →ₗ[ℂ] V₃)
    (arguments : Fin 3 → QuotientState parameters) :
    stateTrilinearMultilinear operation firstMap secondMap thirdMap arguments =
      operation (firstMap (arguments 0)) (secondMap (arguments 1)) (thirdMap (arguments 2)) :=
  rfl

/-- The constant zero-slot multilinear term. -/
def stateConstantMultilinear (value : ACore parameters 1) :
    MultilinearMap ℂ (fun _ : Fin 0 => QuotientState parameters) (ACore parameters 1) :=
  MultilinearMap.constOfIsEmpty ℂ (fun _ : Fin 0 => QuotientState parameters) value

@[simp] theorem stateConstantMultilinear_apply (value : ACore parameters 1)
    (arguments : Fin 0 → QuotientState parameters) :
    stateConstantMultilinear value arguments = value := rfl

/-- One extra scalar `epsilon` slot in front of an existing term. -/
def stateScalarWrap {slots : ℕ}
    (term : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters)
      (ACore parameters 1)) :
    MultilinearMap ℂ (fun _ : Fin (slots + 1) => QuotientState parameters)
      (ACore parameters 1) where
  toFun arguments := stateScalar (arguments 0) • term (fun position => arguments position.succ)
  map_update_add' := by
    intro _ arguments slot first second
    rcases Fin.eq_zero_or_eq_succ slot with rfl | ⟨tail, rfl⟩
    · have argsUnchanged (replacement : QuotientState parameters) :
          (fun position : Fin slots =>
            Function.update arguments 0 replacement position.succ) =
          (fun position => arguments position.succ) := by
        funext position
        exact Function.update_of_ne (Fin.succ_ne_zero position) replacement arguments
      rw [argsUnchanged, argsUnchanged, argsUnchanged, Function.update_self,
        Function.update_self, Function.update_self, map_add, add_smul]
    · have scalarUnchanged (replacement : QuotientState parameters) :
          Function.update arguments tail.succ replacement 0 = arguments 0 :=
        Function.update_of_ne (Fin.succ_ne_zero tail).symm replacement arguments
      have shifted (replacement : QuotientState parameters) :
          (fun position : Fin slots =>
            Function.update arguments tail.succ replacement position.succ) =
          Function.update (fun position => arguments position.succ) tail replacement := by
        funext position
        by_cases same : position = tail
        · subst same
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne (fun collide => same (Fin.succ_injective _ collide)),
            Function.update_of_ne same]
      rw [shifted, shifted, shifted, scalarUnchanged, scalarUnchanged, scalarUnchanged,
        term.map_update_add, smul_add]
  map_update_smul' := by
    intro _ arguments slot scalar argument
    rcases Fin.eq_zero_or_eq_succ slot with rfl | ⟨tail, rfl⟩
    · have argsUnchanged (replacement : QuotientState parameters) :
          (fun position : Fin slots =>
            Function.update arguments 0 replacement position.succ) =
          (fun position => arguments position.succ) := by
        funext position
        exact Function.update_of_ne (Fin.succ_ne_zero position) replacement arguments
      rw [argsUnchanged, argsUnchanged, Function.update_self, Function.update_self,
        map_smul, smul_assoc]
    · have scalarUnchanged (replacement : QuotientState parameters) :
          Function.update arguments tail.succ replacement 0 = arguments 0 :=
        Function.update_of_ne (Fin.succ_ne_zero tail).symm replacement arguments
      have shifted (replacement : QuotientState parameters) :
          (fun position : Fin slots =>
            Function.update arguments tail.succ replacement position.succ) =
          Function.update (fun position => arguments position.succ) tail replacement := by
        funext position
        by_cases same : position = tail
        · subst same
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne (fun collide => same (Fin.succ_injective _ collide)),
            Function.update_of_ne same]
      rw [shifted, shifted, scalarUnchanged, scalarUnchanged, term.map_update_smul,
        smul_comm]

@[simp] theorem stateScalarWrap_apply {slots : ℕ}
    (term : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters)
      (ACore parameters 1))
    (arguments : Fin (slots + 1) → QuotientState parameters) :
    stateScalarWrap term arguments =
      stateScalar (arguments 0) • term (fun position => arguments position.succ) := rfl

/-- Insertion of a scalar-row term into one of the four quotient rows. -/
def rowInsert (row : Fin 4) {slots : ℕ}
    (term : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters)
      (ACore parameters 1)) :
    MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters)
      (QuotientRows parameters) :=
  (LinearMap.single ℂ (fun _ : Fin 4 => ACore parameters 1) row).compMultilinearMap term

@[simp] theorem rowInsert_apply (row : Fin 4) {slots : ℕ}
    (term : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters)
      (ACore parameters 1))
    (arguments : Fin slots → QuotientState parameters) :
    rowInsert row term arguments = Pi.single row (term arguments) := rfl

end Grad.NonlinearQuotientBounds
