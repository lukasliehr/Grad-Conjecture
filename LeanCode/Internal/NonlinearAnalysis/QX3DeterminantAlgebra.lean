import QX2RawFirstPair

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.RawForward

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.NonlinearProduct Grad.QuotientProjection Grad.AxisSplit

variable {parameters : PhaseParameters}

def swapFirstCells (cell : ℤ) : CellAssignments 3 cell ≃ CellAssignments 3 cell where
  toFun assignment := ⟨![assignment.val 1, assignment.val 0, assignment.val 2], by
    have total := assignment.property
    rw [Fin.sum_univ_three]
    change assignment.val 1 + assignment.val 0 + assignment.val 2 = cell
    simpa only [Fin.sum_univ_three, add_comm (assignment.val 1) (assignment.val 0)] using total⟩
  invFun assignment := ⟨![assignment.val 1, assignment.val 0, assignment.val 2], by
    have total := assignment.property
    rw [Fin.sum_univ_three]
    change assignment.val 1 + assignment.val 0 + assignment.val 2 = cell
    simpa only [Fin.sum_univ_three, add_comm (assignment.val 1) (assignment.val 0)] using total⟩
  left_inv assignment := by
    apply Subtype.ext
    funext index
    fin_cases index <;> rfl
  right_inv assignment := by
    apply Subtype.ext
    funext index
    fin_cases index <;> rfl

theorem determinantMultilinear_swap (first second third : ComplexEuclidean 3) :
    determinantMultilinear ![second, first, third] = -determinantMultilinear ![first, second, third] := by
  ext coordinate
  fin_cases coordinate
  change determinantMultilinear ![second, first, third] 0 = -determinantMultilinear ![first, second, third] 0
  rw [determinantMultilinear_value, determinantMultilinear_value,
    Grad.NonlinearQuotient.complexDeterminant_eq, Grad.NonlinearQuotient.complexDeterminant_eq]
  ring

/-- Alternation of the actual coefficient convolution determinant. The
Fourier indices are reindexed, rather than treating them as pointwise products. -/
theorem determinantOperation_swap (first second third : ACore parameters 3) :
    determinantOperation parameters second first third = -determinantOperation parameters first second third := by
  apply acore_ext
  intro cell point
  change ((tripleProductLinear parameters determinantMultilinear second first third).val cell).value point = _
  rw [tripleProductLinear_apply, actualMultilinearProduct_isActual,
    acore_val_neg, closedJet_value_neg, ContinuousMap.neg_apply]
  change productCoefficientValue determinantMultilinear ![second, first, third] cell point =
    -((tripleProductLinear parameters determinantMultilinear first second third).val cell).value point
  rw [tripleProductLinear_apply, actualMultilinearProduct_isActual]
  unfold productCoefficientValue
  rw [← (swapFirstCells cell).tsum_eq, ← tsum_neg]
  apply tsum_congr
  intro assignment
  change determinantMultilinear ![(second.val (assignment.val 1)).value point,
      (first.val (assignment.val 0)).value point, (third.val (assignment.val 2)).value point] =
    -determinantMultilinear ![(first.val (assignment.val 0)).value point,
      (second.val (assignment.val 1)).value point, (third.val (assignment.val 2)).value point]
  exact determinantMultilinear_swap _ _ _

theorem determinantOperation_self (field third : ACore parameters 3) :
    determinantOperation parameters field field third = 0 := by
  have negative := determinantOperation_swap field field third
  have doubled : (2 : ℂ) • determinantOperation parameters field field third = 0 := by
    calc
      _ = determinantOperation parameters field field third + determinantOperation parameters field field third := by module
      _ = 0 := eq_neg_iff_add_eq_zero.mp negative
  exact (smul_eq_zero.mp doubled).resolve_left (by norm_num)

/-- Spatial coordinate multiplication passes through any selected slot
of the actual convolution product, with no commutativity assumption. -/
theorem actualProduct_coordinate {arity inputDimension outputDimension : ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin (arity + 1) => ComplexEuclidean inputDimension) (ComplexEuclidean outputDimension))
    (fields : Fin (arity + 1) → ACore parameters inputDimension) (slot : Fin (arity + 1))
    (coordinate : Fin 2) :
    actualMultilinearProduct parameters multiplication
      (Function.update fields slot (coordinateCore parameters coordinate (fields slot))) =
    coordinateCore parameters coordinate (actualMultilinearProduct parameters multiplication fields) := by
  classical
  apply acore_ext
  intro cell point
  rw [actualMultilinearProduct_isActual, coordinateCore_val, coordinateJet_value,
    actualMultilinearProduct_isActual]
  unfold productCoefficientValue
  rw [← tsum_const_smul'' (point.val coordinate)]
  apply tsum_congr
  intro assignment
  have tuple : (fun index =>
      ((Function.update fields slot (coordinateCore parameters coordinate (fields slot)) index).val
        (assignment.val index)).value point) =
    Function.update (fun index => ((fields index).val (assignment.val index)).value point) slot
      (point.val coordinate • ((fields slot).val (assignment.val slot)).value point) := by
    funext index
    by_cases same : index = slot
    · subst index
      simp only [Function.update_self, coordinateCore_val, coordinateJet_value]
    · simp only [Function.update_of_ne same]
  rw [tuple, ← Complex.coe_smul, multiplication.map_update_smul]
  simp only [Function.update_eq_self, Complex.coe_smul]

end Grad.RawForward
