import GC14SeedRealization
import GC14SeedBounds

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity

def seedBasis (coordinate : Fin 2) : ComplexEuclidean 2 :=
  WithLp.toLp 2 (Pi.single coordinate 1)

def seedColumn (matrix : OperatorValue 2 2) (coordinate : Fin 2) : OperatorValue 1 2 :=
  columnEmbedding 1 2 0 (matrix (seedBasis coordinate))

def seedRow (coordinate : Fin 2) : OperatorValue 2 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun vector => WithLp.toLp 2 fun _ : Fin 1 => vector coordinate
      map_add' := by
        intro first second
        apply PiLp.ext
        intro index
        rfl
      map_smul' := by
        intro scalar vector
        apply PiLp.ext
        intro index
        rfl }

theorem seedRow_apply (coordinate : Fin 2) (vector : ComplexEuclidean 2) (index : Fin 1) :
    seedRow coordinate vector index = vector coordinate := rfl

theorem seedBasis_decomposition (vector : ComplexEuclidean 2) :
    (∑ coordinate : Fin 2, vector coordinate • seedBasis coordinate) = vector := by
  apply PiLp.ext
  intro index
  fin_cases index <;> simp [Fin.sum_univ_two, seedBasis]

theorem seedScalarLift_operator (matrix : OperatorValue 2 2) (scalar : ℂ) :
    (∑ coordinate : Fin 2, (seedColumn matrix coordinate).comp
      ((scalar • ContinuousLinearMap.id ℂ (ComplexEuclidean 1)).comp (seedRow coordinate))) =
      scalar • matrix := by
  apply ContinuousLinearMap.ext
  intro vector
  change (∑ coordinate : Fin 2,
    (seedColumn matrix coordinate) ((scalar • ContinuousLinearMap.id ℂ (ComplexEuclidean 1))
      (seedRow coordinate vector))) = scalar • matrix vector
  simp only [seedColumn, columnEmbedding_apply, smul_apply,
    ContinuousLinearMap.id_apply, PiLp.smul_apply, seedRow_apply, smul_eq_mul]
  calc
    _ = scalar • matrix (∑ coordinate : Fin 2, vector coordinate • seedBasis coordinate) := by
      rw [map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [map_smul, smul_smul]
    _ = _ := by rw [seedBasis_decomposition]

/-- Lift the scalar one-dimensional coefficient by exact rank-one matrix
products, reusing the closed coefficient algebra. -/
def seedScalarLift {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade : ℕ}
    (matrix : OperatorValue 2 2) (coefficient : Coefficient L sigma gamma ell grade 1 1) :
    Coefficient L sigma gamma ell grade 2 2 :=
  ∑ coordinate : Fin 2, coefficientComposition admissible grade
    (seedConstantCell L sigma gamma ell grade 0 (seedColumn matrix coordinate))
    (coefficientComposition admissible grade coefficient
      (seedConstantCell L sigma gamma ell grade 0 (seedRow coordinate)))

theorem seedScalarLift_fourier {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    (matrix : OperatorValue 2 2) (coefficient : Coefficient L sigma gamma ell 0 1 1)
    (angle : ℝ) (point : ClosedDisk) (scalar : ℂ)
    (realization : fourierEvaluation coefficient angle point =
      scalar • ContinuousLinearMap.id ℂ (ComplexEuclidean 1)) :
    fourierEvaluation (seedScalarLift admissible matrix coefficient) angle point = scalar • matrix := by
  change seedFourierCLM admissible 2 2 angle point (∑ coordinate : Fin 2, _) = _
  rw [map_sum]
  change (∑ coordinate : Fin 2, fourierEvaluation
    (coefficientComposition admissible 0 _ (coefficientComposition admissible 0 coefficient _))
      angle point) = _
  simp_rw [fourierComposition, seedConstantCell_fourier, realization]
  have phaseZero : fourierPhase 0 angle = 1 := by simp [fourierPhase]
  simp only [phaseZero, one_smul]
  exact seedScalarLift_operator matrix scalar

theorem seedZeroCell_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (value : OperatorValue inputDimension outputDimension) :
    ‖seedConstantCell L sigma gamma ell grade 0 value‖ ≤
      (Fintype.card (DerivativeIndex grade) : ℝ) * ‖value‖ := by
  have zeroFrequency : Grad.CartesianState.cellFrequency 0 = 1 := by
    norm_num [Grad.CartesianState.cellFrequency_formula]
  simpa only [Int.cast_zero, abs_zero, mul_zero, Real.exp_zero, zeroFrequency, one_pow, one_mul]
    using seedConstantCell_norm_le admissible (grade := grade) 0 value

def seedScalarLiftConstant (grade : ℕ) (matrix : OperatorValue 2 2) : ℝ :=
  gradeProductConstant grade ^ 2 * (Fintype.card (DerivativeIndex grade) : ℝ) ^ 2 *
    ∑ coordinate : Fin 2, ‖seedColumn matrix coordinate‖ * ‖seedRow coordinate‖

theorem seedScalarLiftConstant_nonnegative (grade : ℕ) (matrix : OperatorValue 2 2) :
    0 ≤ seedScalarLiftConstant grade matrix := by
  unfold seedScalarLiftConstant
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (Finset.sum_nonneg fun coordinate _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem seedScalarLift_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade : ℕ}
    (matrix : OperatorValue 2 2) (coefficient : Coefficient L sigma gamma ell grade 1 1) :
    ‖seedScalarLift admissible matrix coefficient‖ ≤
      seedScalarLiftConstant grade matrix * ‖coefficient‖ := by
  have productPositive := seedProductConstant_nonnegative grade
  have each (coordinate : Fin 2) :
      ‖coefficientComposition admissible grade
        (seedConstantCell L sigma gamma ell grade 0 (seedColumn matrix coordinate))
        (coefficientComposition admissible grade coefficient
          (seedConstantCell L sigma gamma ell grade 0 (seedRow coordinate)))‖ ≤
      (gradeProductConstant grade ^ 2 * (Fintype.card (DerivativeIndex grade) : ℝ) ^ 2 *
        (‖seedColumn matrix coordinate‖ * ‖seedRow coordinate‖)) * ‖coefficient‖ := by
    calc
      _ ≤ gradeProductConstant grade *
          ‖seedConstantCell L sigma gamma ell grade 0 (seedColumn matrix coordinate)‖ *
          ‖coefficientComposition admissible grade coefficient
            (seedConstantCell L sigma gamma ell grade 0 (seedRow coordinate))‖ :=
        coefficientComposition_norm_le admissible grade _ _
      _ ≤ (gradeProductConstant grade *
          ((Fintype.card (DerivativeIndex grade) : ℝ) * ‖seedColumn matrix coordinate‖)) *
          (gradeProductConstant grade * ‖coefficient‖ *
            ((Fintype.card (DerivativeIndex grade) : ℝ) * ‖seedRow coordinate‖)) := by
        apply mul_le_mul
          (mul_le_mul_of_nonneg_left (seedZeroCell_norm_le admissible _) productPositive)
        · exact (coefficientComposition_norm_le admissible grade _ _).trans
            (mul_le_mul_of_nonneg_left (seedZeroCell_norm_le admissible _)
              (mul_nonneg productPositive (norm_nonneg coefficient)))
        · exact norm_nonneg _
        · exact mul_nonneg productPositive (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  unfold seedScalarLift
  calc
    _ ≤ ∑ coordinate : Fin 2, ‖coefficientComposition admissible grade
        (seedConstantCell L sigma gamma ell grade 0 (seedColumn matrix coordinate))
        (coefficientComposition admissible grade coefficient
          (seedConstantCell L sigma gamma ell grade 0 (seedRow coordinate)))‖ := norm_sum_le _ _
    _ ≤ ∑ coordinate : Fin 2,
        (gradeProductConstant grade ^ 2 * (Fintype.card (DerivativeIndex grade) : ℝ) ^ 2 *
          (‖seedColumn matrix coordinate‖ * ‖seedRow coordinate‖)) * ‖coefficient‖ :=
      Finset.sum_le_sum fun coordinate _ => each coordinate
    _ = _ := by
      unfold seedScalarLiftConstant
      rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem seedScalarLift_realizes {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade : ℕ}
    (matrix : OperatorValue 2 2)
    {base : Coefficient L sigma gamma ell 0 1 1} {graded : Coefficient L sigma gamma ell grade 1 1}
    (realizes : RealizesSameCoefficient base graded) :
    RealizesSameCoefficient (seedScalarLift admissible matrix base) (seedScalarLift admissible matrix graded) := by
  intro cell point
  change coefficientDerivative (∑ coordinate : Fin 2, _) cell
      (Grad.GaugeCoefficients.Neumann.Regularity.zeroDerivativeIndexAt grade) point =
    coefficientDerivative (∑ coordinate : Fin 2, _) cell zeroDerivativeIndex point
  rw [seedDerivative_sum, seedDerivative_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  exact seedComposition_realizes admissible
    (seedConstantCell_realizes L sigma gamma ell grade 0 (seedColumn matrix coordinate))
    (seedComposition_realizes admissible realizes
      (seedConstantCell_realizes L sigma gamma ell grade 0 (seedRow coordinate))) cell point

end Grad.GaugeCoefficients.Physical.Frame
