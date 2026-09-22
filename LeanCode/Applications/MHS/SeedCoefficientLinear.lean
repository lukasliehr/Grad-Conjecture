import SeedExponentialSmooth

noncomputable section

open scoped ContDiff

namespace Grad.Constraints.Seed

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Frame

theorem coefficient_ext {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    {first second : Coefficient L sigma gamma ell grade inputDimension outputDimension}
    (equal : ∀ cell index point, coefficientDerivative first cell index point = coefficientDerivative second cell index point) :
    first = second := by
  apply Subtype.ext
  apply lp.ext
  funext pair
  apply ContinuousMap.ext
  intro point
  change weightedDerivative first pair.1 pair.2 point = weightedDerivative second pair.1 pair.2 point
  rw [weighted_derivative_literal, weighted_derivative_literal, equal]

def constantCellLinear (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ) (cell : ℤ) :
    OperatorValue inputDimension outputDimension →ₗ[ℂ] Coefficient L sigma gamma ell grade inputDimension outputDimension where
  toFun := seedConstantCell L sigma gamma ell grade cell
  map_add' first second := by
    apply coefficient_ext
    intro other index point
    simp only [coefficientDerivative_add_apply, seedConstantCell_derivative]
    split_ifs <;> simp
  map_smul' scalar value := by
    apply coefficient_ext
    intro other index point
    simp only [coefficientDerivative_smul_apply, seedConstantCell_derivative]
    split_ifs <;> try rfl
    all_goals
      apply ContinuousLinearMap.ext
      intro vector
      apply PiLp.ext
      intro coordinate
      change (0 : ℂ) = scalar * 0
      ring

def constantCellCLM {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade inputDimension outputDimension : ℕ) (cell : ℤ) :
    OperatorValue inputDimension outputDimension →L[ℂ] Coefficient L sigma gamma ell grade inputDimension outputDimension :=
  (constantCellLinear L sigma gamma ell grade inputDimension outputDimension cell).mkContinuous
    ((Fintype.card (DerivativeIndex grade) : ℝ) *
      (Real.exp (sigma * |(cell : ℝ)|) * cellFrequency cell ^ grade))
    (fun value => (seedConstantCell_norm_le admissible cell value).trans_eq (by ring))

theorem constantCellCLM_apply {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade inputDimension outputDimension : ℕ) (cell : ℤ) (value : OperatorValue inputDimension outputDimension) :
    constantCellCLM admissible grade inputDimension outputDimension cell value =
      seedConstantCell L sigma gamma ell grade cell value := rfl

theorem compose_add_outer {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) {i m o : ℕ}
    (first second : Coefficient L sigma gamma ell grade m o) (inner : Coefficient L sigma gamma ell grade i m) :
    coefficientComposition admissible grade (first + second) inner =
      coefficientComposition admissible grade first inner + coefficientComposition admissible grade second inner := by
  apply Subtype.ext
  exact rawComposition_add_outer admissible grade first.val second.val inner.val

theorem compose_add_inner {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) {i m o : ℕ}
    (outer : Coefficient L sigma gamma ell grade m o) (first second : Coefficient L sigma gamma ell grade i m) :
    coefficientComposition admissible grade outer (first + second) =
      coefficientComposition admissible grade outer first + coefficientComposition admissible grade outer second := by
  apply Subtype.ext
  exact rawComposition_add_inner admissible grade outer.val first.val second.val

theorem compose_smul_outer {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) {i m o : ℕ} (scalar : ℂ)
    (outer : Coefficient L sigma gamma ell grade m o) (inner : Coefficient L sigma gamma ell grade i m) :
    coefficientComposition admissible grade (scalar • outer) inner =
      scalar • coefficientComposition admissible grade outer inner := by
  apply Subtype.ext
  exact rawComposition_smul_outer admissible grade scalar outer.val inner.val

theorem compose_smul_inner {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) {i m o : ℕ} (scalar : ℂ)
    (outer : Coefficient L sigma gamma ell grade m o) (inner : Coefficient L sigma gamma ell grade i m) :
    coefficientComposition admissible grade outer (scalar • inner) =
      scalar • coefficientComposition admissible grade outer inner := by
  apply Subtype.ext
  exact rawComposition_smul_inner admissible grade scalar outer.val inner.val

def scalarLiftLinear {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (matrix : OperatorValue 2 2) :
    Coefficient L sigma gamma ell grade 1 1 →ₗ[ℂ] Coefficient L sigma gamma ell grade 2 2 where
  toFun := seedScalarLift admissible matrix
  map_add' first second := by
    simp only [seedScalarLift, compose_add_outer, compose_add_inner, Finset.sum_add_distrib]
  map_smul' scalar value := by
    simp only [seedScalarLift, compose_smul_outer, compose_smul_inner, Finset.smul_sum, RingHom.id_apply]

def scalarLiftCLM {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (matrix : OperatorValue 2 2) :
    Coefficient L sigma gamma ell grade 1 1 →L[ℂ] Coefficient L sigma gamma ell grade 2 2 :=
  (scalarLiftLinear admissible grade matrix).mkContinuous (seedScalarLiftConstant grade matrix)
    (seedScalarLift_norm_le admissible matrix)

theorem scalarLiftCLM_apply {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (matrix : OperatorValue 2 2) (coefficient : Coefficient L sigma gamma ell grade 1 1) :
    scalarLiftCLM admissible grade matrix coefficient = seedScalarLift admissible matrix coefficient := rfl

end Grad.Constraints.Seed
