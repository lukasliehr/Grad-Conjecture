import COR12Consumer
import JInterpolation
import AQ3Consumers

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState Grad.FourierGrade

def originalGradeNorm {dimension : ℕ} {parameters : PhaseParameters}
    (grade : ℕ) (field : ACore parameters dimension) : ℝ :=
  ‖GradeCore.ofCoreLinear (grade := grade) field‖

theorem originalGradeNorm_nonnegative {dimension : ℕ} {parameters : PhaseParameters}
    (grade : ℕ) (field : ACore parameters dimension) : 0 ≤ originalGradeNorm grade field := norm_nonneg _

/-- The actual p-fold cell convolution of a fixed complex-multilinear
physical product. No phase multiplication or projection changes the fields. -/
def productCoefficientValue {arity outputDimension : ℕ} {dimensions : Fin arity → ℕ}
    {parameters : PhaseParameters}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ACore parameters (dimensions index))
    (cell : ℤ) (point : ClosedDisk) : ComplexEuclidean outputDimension :=
  ∑' cells : {indices : Fin arity → ℤ // ∑ index, indices index = cell},
    multiplication (fun index => ((fields index).val (cells.val index)).value point)

def IsActualMultilinearProduct {arity outputDimension : ℕ} {dimensions : Fin arity → ℕ}
    {parameters : PhaseParameters}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ACore parameters (dimensions index))
    (product : ACore parameters outputDimension) : Prop :=
  ∀ cell point, (product.val cell).value point = productCoefficientValue multiplication fields cell point

/-- Construction is an output, not an assumed continuity or product law. -/
def ProductConstructionGoal : Prop :=
  ∀ arity : ℕ, 2 ≤ arity → ∀ (dimensions : Fin arity → ℕ) (outputDimension : ℕ)
    (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ACore parameters (dimensions index)),
    ∃! product, IsActualMultilinearProduct multiplication fields product

/-- Exact Q2: all arities, original norms and unchanged phase parameters;
one q+3 factor and all other factors at the fixed grade three. -/
def OneHighProductBoundGoal : Prop :=
  ∀ arity : ℕ, 2 ≤ arity → ∀ grade : ℕ, ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (dimensions : Fin arity → ℕ) (outputDimension : ℕ) (parameters : PhaseParameters)
      (multiplication : ContinuousMultilinearMap ℂ
        (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
      (fields : (index : Fin arity) → ACore parameters (dimensions index))
      (product : ACore parameters outputDimension),
      IsActualMultilinearProduct multiplication fields product →
      originalGradeNorm grade product ≤ constant * ‖multiplication‖ *
        ∑ index, originalGradeNorm (grade + 3) (fields index) *
          ∏ other ∈ Finset.univ.erase index, originalGradeNorm 3 (fields other)

def ProductBlockGoal : Prop := ProductConstructionGoal ∧ OneHighProductBoundGoal

end Grad.NonlinearProduct
