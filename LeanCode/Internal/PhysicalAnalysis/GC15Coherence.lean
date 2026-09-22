import GC15GradeSlots

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Allocation

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Frame

theorem FamilyCoherent.add {L sigma gamma ell : ℝ} {input output : ℕ}
    {first second : CoefficientFamily L sigma gamma ell input output}
    (firstCoherent : FamilyCoherent first) (secondCoherent : FamilyCoherent second) :
    FamilyCoherent (fun grade => first grade + second grade) := by
  intro grade other index otherIndex same cell point
  simp only [coefficientDerivative_add_apply]
  rw [firstCoherent grade other index otherIndex same cell point,
    secondCoherent grade other index otherIndex same cell point]

theorem FamilyCoherent.smul {L sigma gamma ell : ℝ} {input output : ℕ}
    {family : CoefficientFamily L sigma gamma ell input output}
    (coherent : FamilyCoherent family) (scalar : ℂ) :
    FamilyCoherent (fun grade => scalar • family grade) := by
  intro grade other index otherIndex same cell point
  simp only [coefficientDerivative_smul_apply]
  rw [coherent grade other index otherIndex same cell point]

theorem FamilyCoherent.sub {L sigma gamma ell : ℝ} {input output : ℕ}
    {first second : CoefficientFamily L sigma gamma ell input output}
    (firstCoherent : FamilyCoherent first) (secondCoherent : FamilyCoherent second) :
    FamilyCoherent (fun grade => first grade - second grade) := by
  simpa only [neg_one_smul, sub_eq_add_neg] using firstCoherent.add (secondCoherent.smul (-1))

def multiIndexAtOrder (index : CartesianMultiIndex) : DerivativeIndex (cartesianOrder index) :=
  ⟨(⟨index.1, by simp only [cartesianOrder]; omega⟩,
      ⟨index.2, by simp only [cartesianOrder]; omega⟩), by rfl⟩

def rawFamilyDerivative {L sigma gamma ell : ℝ} {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output)
    (cell : ℤ) (index : CartesianMultiIndex) (point : ClosedDisk) : OperatorValue input output :=
  coefficientDerivative (family (cartesianOrder index)) cell (multiIndexAtOrder index) point

theorem coherent_derivative_raw {L sigma gamma ell : ℝ} {input output grade : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (family grade) cell index point =
      rawFamilyDerivative family cell (derivativeMultiIndex index) point := by
  exact coherent grade _ index (multiIndexAtOrder (derivativeMultiIndex index)) rfl cell point

def rawCompositionDerivative {input middle output : ℕ}
    (outer : ℤ → CartesianMultiIndex → ClosedDisk → OperatorValue middle output)
    (inner : ℤ → CartesianMultiIndex → ClosedDisk → OperatorValue input middle)
    (cell : ℤ) (index : CartesianMultiIndex) (point : ClosedDisk) : OperatorValue input output :=
  ∑' first : ℤ, ∑ split : Fin (index.1 + 1) × Fin (index.2 + 1),
    ((Nat.choose index.1 split.1.val * Nat.choose index.2 split.2.val : ℕ) : ℂ) •
      (outer first (split.1.val, split.2.val) point).comp
        (inner (cell - first) (index.1 - split.1.val, index.2 - split.2.val) point)

theorem FamilyCoherent.comp {L sigma gamma ell : ℝ} {input middle output : ℕ}
    (admissible : Admissible L sigma gamma ell)
    {outer : CoefficientFamily L sigma gamma ell middle output}
    {inner : CoefficientFamily L sigma gamma ell input middle}
    (outerCoherent : FamilyCoherent outer) (innerCoherent : FamilyCoherent inner) :
    FamilyCoherent (fun grade => coefficientComposition admissible grade (outer grade) (inner grade)) := by
  intro grade other index otherIndex same cell point
  rw [coefficientComposition_derivative, coefficientComposition_derivative]
  simp only [formalCompositionDerivative]
  simp_rw [coherent_derivative_raw outer outerCoherent, coherent_derivative_raw inner innerCoherent]
  change rawCompositionDerivative (rawFamilyDerivative outer) (rawFamilyDerivative inner)
      cell (derivativeMultiIndex index) point =
    rawCompositionDerivative (rawFamilyDerivative outer) (rawFamilyDerivative inner)
      cell (derivativeMultiIndex otherIndex) point
  rw [same]

theorem evaluateExpression_coherent {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    (assignment : CoefficientAssignment L sigma gamma ell) (coherent : AssignmentCoherent assignment)
    {input output : ℕ} (expression : CoefficientExpression input output) :
    FamilyCoherent (fun grade => evaluateExpression admissible assignment grade expression) := by
  induction expression with
  | atom input output label => exact coherent input output label
  | add first second firstIH secondIH => exact firstIH.add secondIH
  | smul scalar expression ih => exact ih.smul scalar
  | comp outer inner outerIH innerIH => exact FamilyCoherent.comp admissible outerIH innerIH

def compositionLeftLinear {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) {input middle output : ℕ}
    (inner : Coefficient L sigma gamma ell grade input middle) :
    Coefficient L sigma gamma ell grade middle output →ₗ[ℂ]
      Coefficient L sigma gamma ell grade input output where
  toFun outer := coefficientComposition admissible grade outer inner
  map_add' first second := by
    apply Subtype.ext
    exact rawComposition_add_outer admissible grade first.val second.val inner.val
  map_smul' scalar outer := by
    apply Subtype.ext
    exact rawComposition_smul_outer admissible grade scalar outer.val inner.val

def compositionRightLinear {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) {input middle output : ℕ}
    (outer : Coefficient L sigma gamma ell grade middle output) :
    Coefficient L sigma gamma ell grade input middle →ₗ[ℂ]
      Coefficient L sigma gamma ell grade input output where
  toFun inner := coefficientComposition admissible grade outer inner
  map_add' first second := by
    apply Subtype.ext
    exact rawComposition_add_inner admissible grade outer.val first.val second.val
  map_smul' scalar inner := by
    apply Subtype.ext
    exact rawComposition_smul_inner admissible grade scalar outer.val inner.val

theorem composition_deviation_expansion {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) {input middle output : ℕ}
    (outer referenceOuter : Coefficient L sigma gamma ell grade middle output)
    (inner referenceInner : Coefficient L sigma gamma ell grade input middle) :
    coefficientComposition admissible grade outer inner -
      coefficientComposition admissible grade referenceOuter referenceInner =
    coefficientComposition admissible grade (outer - referenceOuter) referenceInner +
      coefficientComposition admissible grade referenceOuter (inner - referenceInner) +
      coefficientComposition admissible grade (outer - referenceOuter) (inner - referenceInner) := by
  have left (first second : Coefficient L sigma gamma ell grade middle output)
      (value : Coefficient L sigma gamma ell grade input middle) :=
    (compositionLeftLinear admissible grade value).map_sub first second
  have right (value : Coefficient L sigma gamma ell grade middle output)
      (first second : Coefficient L sigma gamma ell grade input middle) :=
    (compositionRightLinear admissible grade value).map_sub first second
  change ∀ first second value, coefficientComposition admissible grade (first - second) value =
    coefficientComposition admissible grade first value - coefficientComposition admissible grade second value at left
  change ∀ value first second, coefficientComposition admissible grade value (first - second) =
    coefficientComposition admissible grade value first - coefficientComposition admissible grade value second at right
  rw [left, right, left, right, right]
  abel

end Grad.GaugeCoefficients.Physical.Allocation
