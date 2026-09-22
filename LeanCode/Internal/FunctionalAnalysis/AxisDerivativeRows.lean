import AxisProductOrigin

noncomputable section

open scoped BigOperators

namespace Grad.AxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

/-- The axis value as a complex-linear functional on closed jets. -/
def originValueLinear (dimension : ℕ) : ClosedJet dimension →ₗ[ℂ] ComplexEuclidean dimension where
  toFun := originValue
  map_add' := originValue_add
  map_smul' scalar field := originValue_smul scalar field

/-- The axis first derivative as a complex-linear functional on closed jets. -/
def originPartialLinear (direction : Fin 2) (dimension : ℕ) :
    ClosedJet dimension →ₗ[ℂ] ComplexEuclidean dimension where
  toFun := originPartial direction
  map_add' := originPartial_add direction
  map_smul' scalar field := originPartial_smul direction scalar field

/-- Axis value of one cell of one quotient row, as a linear functional. -/
def rowsOriginValue (row : Fin 4) (cell : ℤ) :
    QuotientRows parameters →ₗ[ℂ] ComplexEuclidean 1 :=
  (((originValueLinear 1).comp (LinearMap.proj cell)).comp
    (originalCoreSubmodule parameters 1).subtype).comp (LinearMap.proj row)

/-- Axis first derivative of one cell of one quotient row, as a linear functional. -/
def rowsOriginPartial (direction : Fin 2) (row : Fin 4) (cell : ℤ) :
    QuotientRows parameters →ₗ[ℂ] ComplexEuclidean 1 :=
  (((originPartialLinear direction 1).comp (LinearMap.proj cell)).comp
    (originalCoreSubmodule parameters 1).subtype).comp (LinearMap.proj row)

@[simp] theorem rowsOriginValue_apply (row : Fin 4) (cell : ℤ)
    (rows : QuotientRows parameters) :
    rowsOriginValue row cell rows = originValue ((rows row).val cell) := rfl

@[simp] theorem rowsOriginPartial_apply (direction : Fin 2) (row : Fin 4) (cell : ℤ)
    (rows : QuotientRows parameters) :
    rowsOriginPartial direction row cell rows =
      originPartial direction ((rows row).val cell) := rfl

/-- The first diagonal derivative is the exact sum of single-slot insertions. -/
theorem diagonalDerivative_one {V E : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup E] [Module ℂ E] {slots : ℕ}
    (W : MultilinearMap ℂ (fun _ : Fin slots => V) E) (base direction : V) :
    diagonalDerivative W 1 base ![direction] =
      ∑ slot : Fin slots, W (Function.update (fun _ => base) slot direction) := by
  unfold diagonalDerivative
  have univInjections : slotInjections 1 slots = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro insertion
    exact mem_slotInjections.mpr (fun first second _ => Subsingleton.elim first second)
  rw [univInjections]
  rw [← (Equiv.funUnique (Fin 1) (Fin slots)).symm.sum_comp
    (fun insertion => W (slotAssign insertion base ![direction]))]
  apply Finset.sum_congr rfl
  intro slot _
  congr 1
  funext position
  by_cases hit : position = slot
  · subst hit
    have occupied := slotAssign_occupied
      (insertion := (Equiv.funUnique (Fin 1) (Fin slots)).symm position)
      (fun first second _ => Subsingleton.elim first second) base ![direction] 0
    have insertionValue : (Equiv.funUnique (Fin 1) (Fin slots)).symm position 0 = position := rfl
    rw [insertionValue] at occupied
    rw [occupied, Function.update_self]
    rfl
  · have free := slotAssign_free (insertion := (Equiv.funUnique (Fin 1) (Fin slots)).symm slot)
      base ![direction] (slot := position) (fun innerPosition =>
        show ¬(Equiv.funUnique (Fin 1) (Fin slots)).symm slot innerPosition = position from
          fun collide => hit ((show slot = position from collide).symm))
    rw [free, Function.update_of_ne hit]

theorem update_base_self {V : Type*} (base direction : V) {slots : ℕ} (slot : Fin slots) :
    Function.update (fun _ : Fin slots => base) slot direction slot = direction := by
  rw [Function.update_self]

theorem update_base_other {V : Type*} (base direction : V) {slots : ℕ}
    {slot other : Fin slots} (ne : other ≠ slot) :
    Function.update (fun _ : Fin slots => base) slot direction other = base := by
  rw [Function.update_of_ne ne]

/-- The five-part split of the first derivative, seen through any linear functional. -/
theorem functional_rowsDerivative_one {W : Type*} [AddCommGroup W] [Module ℂ W]
    (functional : QuotientRows parameters →ₗ[ℂ] W) (cellLength : ℝ)
    (base direction : QuotientState parameters) :
    functional (quotientRowsDerivative parameters cellLength 1 base ![direction]) =
      functional (quotientDegreeOnePart parameters cellLength ![direction]) +
        (∑ slot : Fin 2, functional (quotientDegreeTwoPart parameters cellLength
          (Function.update (fun _ => base) slot direction))) +
        (∑ slot : Fin 3, functional (quotientDegreeThreePart parameters
          (Function.update (fun _ => base) slot direction))) +
        (∑ slot : Fin 4, functional (quotientDegreeFourPart parameters
          (Function.update (fun _ => base) slot direction))) := by
  unfold quotientRowsDerivative
  rw [map_add, map_add, map_add, map_add]
  rw [diagonalDerivative_zero_of_lt _ _ _ _ (by omega : (0 : ℕ) < 1), map_zero, zero_add]
  rw [diagonalDerivative_one, diagonalDerivative_one, diagonalDerivative_one,
    diagonalDerivative_one]
  rw [map_sum, map_sum, map_sum, map_sum]
  have oneSlot : (∑ slot : Fin 1, functional (quotientDegreeOnePart parameters cellLength
      (Function.update (fun _ => base) slot direction))) =
      functional (quotientDegreeOnePart parameters cellLength ![direction]) := by
    rw [Fin.sum_univ_one]
    have tupleEq : Function.update (fun _ : Fin 1 => base) 0 direction = ![direction] := by
      funext position
      have positionZero : position = 0 := Subsingleton.elim position 0
      subst positionZero
      rw [Function.update_self]
      rfl
    rw [tupleEq]
  rw [oneSlot]

end Grad.AxisSplit
