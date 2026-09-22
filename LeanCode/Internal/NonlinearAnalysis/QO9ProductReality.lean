import QO8DifferentialReality

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 800000

open scoped ComplexConjugate BigOperators

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.CompletedReality

variable {parameters : PhaseParameters}

def negateCellAssignments (arity : ℕ) (cell : ℤ) :
    CellAssignments arity cell ≃ CellAssignments arity (-cell) where
  toFun assignment := ⟨fun index => -assignment.val index, by
    rw [Finset.sum_neg_distrib, assignment.property]⟩
  invFun assignment := ⟨fun index => -assignment.val index, by
    rw [Finset.sum_neg_distrib, assignment.property, neg_neg]⟩
  left_inv assignment := by apply Subtype.ext; funext index; exact neg_neg _
  right_inv assignment := by apply Subtype.ext; funext index; exact neg_neg _

/-- Conjugation and integer-cell reversal commute with an actual real
multilinear physical product. No changed Fourier convolution is used. -/
theorem actualMultilinearProduct_conjugate {arity outputDimension inputDimension : ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin (arity + 1) => ComplexEuclidean inputDimension) (ComplexEuclidean outputDimension))
    (real : ∀ values, cartesianPhysicalConjugation outputDimension (multiplication values) =
      multiplication (fun index => cartesianPhysicalConjugation inputDimension (values index)))
    (fields : Fin (arity + 1) → ACore parameters inputDimension) :
    cartesianCoreConjugation parameters (actualMultilinearProduct parameters multiplication fields) =
      actualMultilinearProduct parameters multiplication
        (fun index => cartesianCoreConjugation parameters (fields index)) := by
  apply acore_ext
  intro cell point
  change cartesianPhysicalConjugation outputDimension
    (((actualMultilinearProduct parameters multiplication fields).val (-cell)).value point) = _
  rw [actualMultilinearProduct_isActual, actualMultilinearProduct_isActual]
  have mapped : HasSum (fun assignment : CellAssignments (arity + 1) (-cell) =>
      cartesianPhysicalConjugation outputDimension
        (multiplication (fun index => ((fields index).val (assignment.val index)).value point)))
      (cartesianPhysicalConjugation outputDimension (productCoefficientValue multiplication fields (-cell) point)) :=
    (cartesianPhysicalConjugation outputDimension).toContinuousLinearEquiv.toContinuousLinearMap.hasSum
      (productValue_summable (Nat.succ_pos arity) multiplication fields (-cell) point).hasSum
  have reindexed := (negateCellAssignments (arity + 1) cell).hasSum_iff.mpr mapped
  have same : HasSum (fun assignment : CellAssignments (arity + 1) cell =>
      multiplication (fun index =>
        ((cartesianCoreConjugation parameters (fields index)).val (assignment.val index)).value point))
      (cartesianPhysicalConjugation outputDimension (productCoefficientValue multiplication fields (-cell) point)) := by
    apply reindexed.congr_fun
    intro assignment
    exact (real _).symm
  exact same.unique (productValue_summable (Nat.succ_pos arity) multiplication
    (fun index => cartesianCoreConjugation parameters (fields index)) cell point).hasSum

theorem physicalDotProduct_conjugate (values : Fin 2 → ComplexEuclidean 3) :
    cartesianPhysicalConjugation 1 (physicalDotProduct values) =
      physicalDotProduct (fun index => cartesianPhysicalConjugation 3 (values index)) := by
  have tuple : values = ![values 0, values 1] := by ext index; fin_cases index <;> rfl
  rw [tuple]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  change conj (physicalDotProduct ![values 0, values 1] 0) =
    physicalDotProduct ![cartesianPhysicalConjugation 3 (values 0),
      cartesianPhysicalConjugation 3 (values 1)] 0
  rw [physicalDotProduct_value, physicalDotProduct_value]
  simp [Grad.NonlinearQuotient.complexDot, cartesianPhysicalConjugation]

theorem determinantMultilinear_conjugate (values : Fin 3 → ComplexEuclidean 3) :
    cartesianPhysicalConjugation 1 (determinantMultilinear values) =
      determinantMultilinear (fun index => cartesianPhysicalConjugation 3 (values index)) := by
  have tuple : values = ![values 0, values 1, values 2] := by ext index; fin_cases index <;> rfl
  rw [tuple]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  change conj (determinantMultilinear ![values 0, values 1, values 2] 0) =
    determinantMultilinear ![cartesianPhysicalConjugation 3 (values 0),
      cartesianPhysicalConjugation 3 (values 1), cartesianPhysicalConjugation 3 (values 2)] 0
  rw [determinantMultilinear_value, determinantMultilinear_value]
  simp [Grad.NonlinearQuotient.complexDeterminant_eq, cartesianPhysicalConjugation]

theorem dotOperation_conjugate (first second : ACore parameters 3) :
    cartesianCoreConjugation parameters (dotOperation parameters first second) =
      dotOperation parameters (cartesianCoreConjugation parameters first)
        (cartesianCoreConjugation parameters second) := by
  change cartesianCoreConjugation parameters
    (pairProductLinear parameters physicalDotProduct first second) =
    pairProductLinear parameters physicalDotProduct
      (cartesianCoreConjugation parameters first) (cartesianCoreConjugation parameters second)
  rw [pairProductLinear_apply, pairProductLinear_apply]
  have law := actualMultilinearProduct_conjugate (parameters := parameters) physicalDotProduct
    physicalDotProduct_conjugate ![first, second]
  have tuple : (fun index : Fin 2 => cartesianCoreConjugation parameters (![first, second] index)) =
      ![cartesianCoreConjugation parameters first, cartesianCoreConjugation parameters second] := by
    funext index
    fin_cases index <;> rfl
  rw [tuple] at law
  exact law

theorem determinantOperation_conjugate (first second third : ACore parameters 3) :
    cartesianCoreConjugation parameters (determinantOperation parameters first second third) =
      determinantOperation parameters (cartesianCoreConjugation parameters first)
        (cartesianCoreConjugation parameters second) (cartesianCoreConjugation parameters third) := by
  change cartesianCoreConjugation parameters
    (tripleProductLinear parameters determinantMultilinear first second third) =
    tripleProductLinear parameters determinantMultilinear
      (cartesianCoreConjugation parameters first) (cartesianCoreConjugation parameters second)
      (cartesianCoreConjugation parameters third)
  rw [tripleProductLinear_apply, tripleProductLinear_apply]
  have law := actualMultilinearProduct_conjugate (parameters := parameters) determinantMultilinear
    determinantMultilinear_conjugate ![first, second, third]
  have tuple : (fun index : Fin 3 => cartesianCoreConjugation parameters (![first, second, third] index)) =
      ![cartesianCoreConjugation parameters first, cartesianCoreConjugation parameters second,
        cartesianCoreConjugation parameters third] := by
    funext index
    fin_cases index <;> rfl
  rw [tuple] at law
  exact law

end Grad.NonlinearRange
