import AAQ15SameSolutionFluxDiagonals

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

section Weighted
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (angular cell inserted : ℕ)

theorem annularSolutionFluxTrace_decoded_weighted (endpoint : Fin 2) (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data) :
    annularLpDecode angular cell inserted
      (annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint
        (annularWeightedData lower angular cell inserted data grade)) =
      annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data :=
  (annularSolutionFluxTrace_diagonal parameters lower length positive bounded lengthPositive widthHalf widthLength
    (fun mode => (annularGradeWeight angular cell inserted mode)⁻¹) 1 (by norm_num)
    (annularGradeWeight_inv_bound angular cell inserted) endpoint (annularWeightedData lower angular cell inserted data grade)).trans
      (congrArg (annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint)
        (annularDataDecode_weighted lower angular cell inserted data grade))

theorem annularSolutionFluxTrace_hasGrade (endpoint : Fin 2) (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data) :
    HasAnnularLpGrade angular cell inserted (annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data) :=
  (congrArg (HasAnnularLpGrade angular cell inserted)
    (annularSolutionFluxTrace_decoded_weighted parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted endpoint data grade)).mp
      (annularLpDecode_hasGrade angular cell inserted
        (annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint (annularWeightedData lower angular cell inserted data grade)))

theorem annularSolutionFluxTrace_weighted_identity (endpoint : Fin 2) (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data)
    (traceGrade : HasAnnularLpGrade angular cell inserted (annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data)) :
    annularLpWeighted angular cell inserted (annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data) traceGrade =
      annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint (annularWeightedData lower angular cell inserted data grade) := by
  apply annularLpDecode_injective angular cell inserted
  exact (annularLpDecode_weighted angular cell inserted _ traceGrade).trans
    (annularSolutionFluxTrace_decoded_weighted parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted endpoint data grade).symm

theorem annularSolutionFluxTrace_weighted_bound (endpoint : Fin 2) (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data)
    (traceGrade : HasAnnularLpGrade angular cell inserted (annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data)) :
    ‖annularLpWeighted angular cell inserted (annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data) traceGrade‖ ≤
      annularFluxPhysicalTraceConstant lower length *
        (‖annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength (annularWeightedData lower angular cell inserted data grade)‖ +
          ‖(annularWeightedData lower angular cell inserted data grade).1.1‖ +
          ‖(annularWeightedData lower angular cell inserted data grade).1.2.1‖ +
          ‖(annularWeightedData lower angular cell inserted data grade).1.2.2.1‖) := by
  rw [annularSolutionFluxTrace_weighted_identity parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted endpoint data grade traceGrade]
  exact annularSolutionFluxTrace_physical_bound parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint (annularWeightedData lower angular cell inserted data grade)

theorem annularSolutionNaturalPTrace_decoded_weighted (endpoint : Fin 2) (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data) :
    annularLpDecode angular cell inserted
      (annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint
        (annularWeightedData lower angular cell inserted data grade)) =
      annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data :=
  (annularSolutionNaturalPTrace_diagonal parameters lower length positive bounded lengthPositive widthHalf widthLength
    (fun mode => (annularGradeWeight angular cell inserted mode)⁻¹) 1 (by norm_num)
    (annularGradeWeight_inv_bound angular cell inserted) endpoint (annularWeightedData lower angular cell inserted data grade)).trans
      (congrArg (annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint)
        (annularDataDecode_weighted lower angular cell inserted data grade))

theorem annularSolutionNaturalPTrace_hasGrade (endpoint : Fin 2) (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data) :
    HasAnnularLpGrade angular cell inserted (annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data) :=
  (congrArg (HasAnnularLpGrade angular cell inserted)
    (annularSolutionNaturalPTrace_decoded_weighted parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted endpoint data grade)).mp
      (annularLpDecode_hasGrade angular cell inserted
        (annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint (annularWeightedData lower angular cell inserted data grade)))

theorem annularSolutionNaturalPTrace_weighted_identity (endpoint : Fin 2) (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data)
    (traceGrade : HasAnnularLpGrade angular cell inserted (annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data)) :
    annularLpWeighted angular cell inserted (annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data) traceGrade =
      annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint (annularWeightedData lower angular cell inserted data grade) := by
  apply annularLpDecode_injective angular cell inserted
  exact (annularLpDecode_weighted angular cell inserted _ traceGrade).trans
    (annularSolutionNaturalPTrace_decoded_weighted parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted endpoint data grade).symm

theorem annularSolutionNaturalPTrace_weighted_bound (endpoint : Fin 2) (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data)
    (traceGrade : HasAnnularLpGrade angular cell inserted (annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data)) :
    ‖annularLpWeighted angular cell inserted (annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data) traceGrade‖ ≤
      annularFluxPhysicalTraceConstant lower length *
        (‖annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength (annularWeightedData lower angular cell inserted data grade)‖ +
          ‖(annularWeightedData lower angular cell inserted data grade).1.1‖ +
          ‖(annularWeightedData lower angular cell inserted data grade).1.2.1‖ +
          ‖(annularWeightedData lower angular cell inserted data grade).1.2.2.1‖) := by
  rw [annularSolutionNaturalPTrace_weighted_identity parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted endpoint data grade traceGrade]
  exact annularSolutionNaturalPTrace_physical_bound parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint (annularWeightedData lower angular cell inserted data grade)

end Weighted
end Grad.AnnularFluxTrace
