import GC14Coefficient

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Envelope

/-- A literal matrix column: `x ↦ x_column • value`. -/
def columnEmbedding (inputDimension outputDimension : ℕ) (column : Fin inputDimension) :
    ComplexEuclidean outputDimension →L[ℂ] OperatorValue inputDimension outputDimension :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => (PiLp.proj 2 (fun _ : Fin inputDimension => ℂ) column).smulRight value
      map_add' := by
        intro first second
        apply ContinuousLinearMap.ext
        intro vector
        exact smul_add (vector column) first second
      map_smul' := by
        intro scalar value
        apply ContinuousLinearMap.ext
        intro vector
        exact smul_comm (vector column) scalar value }

@[simp] theorem columnEmbedding_apply (inputDimension outputDimension : ℕ)
    (column : Fin inputDimension) (value : ComplexEuclidean outputDimension)
    (vector : ComplexEuclidean inputDimension) :
    columnEmbedding inputDimension outputDimension column value vector = vector column • value := rfl

def matrixColumn (inputDimension outputDimension : ℕ) (column : Fin inputDimension) :
    ComplexEuclidean (inputDimension * outputDimension) →L[ℂ] ComplexEuclidean outputDimension :=
  LinearMap.toContinuousLinearMap
    { toFun := fun coefficients => WithLp.toLp 2 fun row => coefficients (finProdFinEquiv (column, row))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- The actual rectangular matrix operator with coefficient entry
`(column,row) ↦ a_(column*outputDimension+row)`. -/
def matrixEmbedding (inputDimension outputDimension : ℕ) :
    ComplexEuclidean (inputDimension * outputDimension) →L[ℂ]
      OperatorValue inputDimension outputDimension :=
  ∑ column : Fin inputDimension,
    (columnEmbedding inputDimension outputDimension column).comp
      (matrixColumn inputDimension outputDimension column)

theorem matrixEmbedding_apply (inputDimension outputDimension : ℕ)
    (coefficients : ComplexEuclidean (inputDimension * outputDimension))
    (vector : ComplexEuclidean inputDimension) (row : Fin outputDimension) :
    matrixEmbedding inputDimension outputDimension coefficients vector row =
      ∑ column : Fin inputDimension, vector column * coefficients (finProdFinEquiv (column, row)) := by
  simp only [matrixEmbedding, sum_apply, ContinuousLinearMap.comp_apply, columnEmbedding_apply]
  change (PiLp.proj 2 (fun _ : Fin outputDimension => ℂ) row :
    ComplexEuclidean outputDimension →L[ℂ] ℂ)
    (∑ column : Fin inputDimension, vector column • matrixColumn inputDimension outputDimension column
      coefficients) = _
  rw [map_sum]
  rfl

def vectorOriginalCoefficient {dimension grade : ℕ} (parameters : PhaseParameters) (L ell : ℝ)
    (field : GradeCore parameters dimension (grade + 3)) :
    Coefficient L parameters.sigma0 parameters.gamma ell grade 1 dimension :=
  originalCoefficient parameters L ell grade (columnEmbedding 1 dimension 0) field.toCore

def matrixOriginalCoefficient {inputDimension outputDimension grade : ℕ}
    (parameters : PhaseParameters) (L ell : ℝ)
    (field : GradeCore parameters (inputDimension * outputDimension) (grade + 3)) :
    Coefficient L parameters.sigma0 parameters.gamma ell grade inputDimension outputDimension :=
  originalCoefficient parameters L ell grade (matrixEmbedding inputDimension outputDimension) field.toCore

theorem vectorOriginalCoefficient_norm_bound {dimension grade : ℕ} {L ell : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : GradeCore parameters dimension (grade + 3)) :
    ‖vectorOriginalCoefficient parameters L ell field‖ ≤
      (originalCoefficientConstant parameters grade * ‖columnEmbedding 1 dimension 0‖) * ‖field‖ :=
  originalCoefficient_norm_bound parameters admissible _ field

theorem matrixOriginalCoefficient_norm_bound {inputDimension outputDimension grade : ℕ} {L ell : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : GradeCore parameters (inputDimension * outputDimension) (grade + 3)) :
    ‖matrixOriginalCoefficient parameters L ell field‖ ≤
      (originalCoefficientConstant parameters grade * ‖matrixEmbedding inputDimension outputDimension‖) *
        ‖field‖ := originalCoefficient_norm_bound parameters admissible _ field

end Grad.GaugeCoefficients.Physical
