import AAQ14FluxGraphDiagonals

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFluxTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace

section SameInverse
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (coefficient : HighAnnularMode → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (coefficientBound : ∀ mode, |coefficient mode| ≤ constant)

theorem annularRecoveredQ_diagonal (field : annularEnergySpace lower length positive) (source : AnnularBulk lower) :
    annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength
      (annularEnergyDiagonal lower length positive coefficient constant nonnegative coefficientBound field)
      (realLpDiagonal coefficient constant nonnegative coefficientBound source) =
      realLpDiagonal coefficient constant nonnegative coefficientBound
        (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source) := by
  simp only [annularRecoveredQ, annularPhysicalDerivative, sub_apply, annularEnergyDerivative_diagonal,
    annularEnergyPhase_diagonal, annularEnergyRadial_diagonal, map_add, map_sub]

/-- Both weak graph coordinates commute with the SAME inverse. Equality of
the derivative follows from the genuine weak graph and equality of q. -/
theorem annularSolvedFlux_diagonal (data : AnnularForcing lower × AnnularBoundary) :
    annularFluxGraphDiagonal lower positive coefficient constant nonnegative coefficientBound
      (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength data) =
      annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength
        (annularDataDiagonal lower coefficient constant nonnegative coefficientBound data) := by
  apply annularFluxWeakGraph_value_injective lower positive bounded
  change realLpDiagonal coefficient constant nonnegative coefficientBound
      (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength
        (annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength data) data.1.1) =
    annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength
      (annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength
        (annularDataDiagonal lower coefficient constant nonnegative coefficientBound data))
      (realLpDiagonal coefficient constant nonnegative coefficientBound data.1.1)
  have qLaw := annularRecoveredQ_diagonal parameters lower length positive lengthPositive widthHalf widthLength
    coefficient constant nonnegative coefficientBound
    (annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength data) data.1.1
  have inverseLaw := annularVariationalInverse_diagonal parameters lower length positive bounded lengthPositive widthHalf widthLength
    coefficient constant nonnegative coefficientBound data
  exact qLaw.symm.trans (congrArg (fun field => annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength
    field (realLpDiagonal coefficient constant nonnegative coefficientBound data.1.1)) inverseLaw)

theorem annularSolutionFluxTrace_diagonal (endpoint : Fin 2) (data : AnnularForcing lower × AnnularBoundary) :
    realLpDiagonal coefficient constant nonnegative coefficientBound
      (annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data) =
      annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint
        (annularDataDiagonal lower coefficient constant nonnegative coefficientBound data) :=
  (annularFluxTrace_diagonal lower positive coefficient constant nonnegative coefficientBound bounded endpoint
    (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength data)).symm.trans
      (congrArg (annularFluxTrace lower positive bounded endpoint)
        (annularSolvedFlux_diagonal parameters lower length positive bounded lengthPositive widthHalf widthLength
          coefficient constant nonnegative coefficientBound data))

theorem annularSolutionNaturalPTrace_diagonal (endpoint : Fin 2) (data : AnnularForcing lower × AnnularBoundary) :
    realLpDiagonal coefficient constant nonnegative coefficientBound
      (annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data) =
      annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint
        (annularDataDiagonal lower coefficient constant nonnegative coefficientBound data) := by
  change realLpDiagonal coefficient constant nonnegative coefficientBound
    (-(annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data)) =
    -(annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint
      (annularDataDiagonal lower coefficient constant nonnegative coefficientBound data))
  rw [map_neg, annularSolutionFluxTrace_diagonal]

end SameInverse
end Grad.AnnularFluxTrace
