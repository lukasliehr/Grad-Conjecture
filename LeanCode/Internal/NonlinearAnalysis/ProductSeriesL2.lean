import ProductCoefficientJet
import ClosedJetIntegralL2

noncomputable section

open scoped ContDiff

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState Grad.Constraints

def wordEvaluationContinuous {dimension order : ℕ} (word : CartesianWord order) :
    C(ClosedDisk, SpatialPlane [×order]→L[ℝ] ComplexEuclidean dimension) →L[ℝ]
      C(ClosedDisk, ComplexEuclidean dimension) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin order => SpatialPlane)
    (ComplexEuclidean dimension) (fun position => spatialBasis (word position))).compLeftContinuous ℝ ClosedDisk

theorem wordEvaluationClosedOperator {Index : Type} {dimension order : ℕ}
    (fields : Index → SpatialPlane → ComplexEuclidean dimension)
    (smooth : ∀ index, ContDiff ℝ ∞ (fields index)) (word : CartesianWord order) (index : Index) :
    wordEvaluationContinuous word (closedOperatorTerm fields smooth order index) =
      closedDerivative (globalClosedJet (fields index) (smooth index)) order word := by
  apply ContinuousMap.ext
  intro point
  exact (globalClosedJet_derivative (fields index) (smooth index) word point).symm

theorem smoothSeriesClosedJet_derivative_hasSum {Index : Type} {dimension order : ℕ}
    (fields : Index → SpatialPlane → ComplexEuclidean dimension)
    (smooth : ∀ index, ContDiff ℝ ∞ (fields index))
    (majorant : ℕ → Index → ℝ) (summable : ∀ order, Summable (majorant order))
    (bounded : ∀ order index point, point ∈ closedUnitDisk →
      ‖iteratedFDeriv ℝ order (fields index) point‖ ≤ majorant order index) (word : CartesianWord order) :
    HasSum (fun index => closedDerivative (globalClosedJet (fields index) (smooth index)) order word)
      (closedDerivative (smoothSeriesClosedJet fields smooth majorant summable bounded) order word) := by
  have mapped := (wordEvaluationContinuous (dimension := dimension) word).hasSum
    (closedOperatorTerm_summable fields smooth majorant summable bounded order).hasSum
  have evaluationEquality : wordEvaluationContinuous (dimension := dimension) word
      (∑' index, closedOperatorTerm fields smooth order index) = smoothSeriesDerivative fields smooth word := by
    apply ContinuousMap.ext
    intro point
    rfl
  rw [evaluationEquality] at mapped
  rw [smoothSeriesClosedJet_derivative]
  simpa only [Function.comp_def, wordEvaluationClosedOperator] using mapped

theorem smoothSeriesClosedJet_L2_hasSum {Index : Type} {dimension order : ℕ}
    (fields : Index → SpatialPlane → ComplexEuclidean dimension)
    (smooth : ∀ index, ContDiff ℝ ∞ (fields index))
    (majorant : ℕ → Index → ℝ) (summable : ∀ order, Summable (majorant order))
    (bounded : ∀ order index point, point ∈ closedUnitDisk →
      ‖iteratedFDeriv ℝ order (fields index) point‖ ≤ majorant order index) (word : CartesianWord order) :
    HasSum (fun index => closedContinuousToDiskL2
      (closedDerivative (globalClosedJet (fields index) (smooth index)) order word))
      (closedContinuousToDiskL2
        (closedDerivative (smoothSeriesClosedJet fields smooth majorant summable bounded) order word)) :=
  (closedValueL2Continuous dimension).hasSum
    (smoothSeriesClosedJet_derivative_hasSum fields smooth majorant summable bounded word)

theorem productCoefficientJet_weighted {arity outputDimension : ℕ} {dimensions : Fin arity → ℕ}
    (positiveArity : 0 < arity) (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ACore parameters (dimensions index)) (cell : ℤ) :
    phaseWeightedJet parameters cell (productCoefficientJet positiveArity parameters multiplication fields cell) =
      weightedProductCoefficientJet positiveArity parameters multiplication fields cell :=
  phaseWeightedJet_inverse_left parameters cell _

theorem weightedProductCoefficientJet_L2_hasSum {arity outputDimension order : ℕ}
    {dimensions : Fin arity → ℕ} (positiveArity : 0 < arity) (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ACore parameters (dimensions index))
    (cell : ℤ) (word : CartesianWord order) :
    HasSum (fun assignment : CellAssignments arity cell => closedContinuousToDiskL2
      (closedDerivative (globalClosedJet
        (weightedProductSmooth parameters assignment.val multiplication
          (fun index => (fields index).val (assignment.val index)))
        (weightedProductSmooth_smooth parameters assignment.val multiplication _)) order word))
      (closedContinuousToDiskL2 (closedDerivative
        (weightedProductCoefficientJet positiveArity parameters multiplication fields cell) order word)) :=
  smoothSeriesClosedJet_L2_hasSum _ _ _ _
    (weightedProductAssignment_bound positiveArity parameters multiplication fields cell) word

end Grad.NonlinearProduct
