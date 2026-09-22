import AAQ16ActualWeightedFluxTraces

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

def HasAnnularFluxGrade (lower : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ)
    (field : annularFluxWeakGraph lower positive) : Prop :=
  HasAnnularLpGrade angular cell inserted field.val.1 ∧ HasAnnularLpGrade angular cell inserted field.val.2

def annularFluxGraphDecode (lower : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ) :
    annularFluxWeakGraph lower positive →L[ℂ] annularFluxWeakGraph lower positive :=
  annularFluxGraphDiagonal lower positive (fun mode => (annularGradeWeight angular cell inserted mode)⁻¹)
    1 (by norm_num) (annularGradeWeight_inv_bound angular cell inserted)

theorem annularFluxGraphDecode_hasGrade (lower : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ)
    (field : annularFluxWeakGraph lower positive) :
    HasAnnularFluxGrade lower positive angular cell inserted (annularFluxGraphDecode lower positive angular cell inserted field) :=
  ⟨annularLpDecode_hasGrade angular cell inserted field.val.1, annularLpDecode_hasGrade angular cell inserted field.val.2⟩

/-- The actual weighted weak graph, using the SAME distributional relation.
No independent weighted inverse or derivative coordinate is assumed. -/
def annularFluxGraphWeighted (lower : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ)
    (field : annularFluxWeakGraph lower positive) (grade : HasAnnularFluxGrade lower positive angular cell inserted field) :
    annularFluxWeakGraph lower positive :=
  ⟨(annularLpWeighted angular cell inserted field.val.1 grade.1,
    annularLpWeighted angular cell inserted field.val.2 grade.2), by
    intro mode
    change CollarWeakDerivative lower
      (radialOrdinary 1 lower positive ((annularGradeWeight angular cell inserted mode : ℂ) • field.val.1 mode))
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 : ℝ) •
        radialOrdinary 1 lower positive ((annularGradeWeight angular cell inserted mode : ℂ) • field.val.2 mode))
    rw [map_smul, map_smul, smul_comm]
    exact collarWeakDerivative_complex_smul lower (annularGradeWeight angular cell inserted mode : ℂ) _ _ (field.property mode)⟩

theorem annularFluxGraphDecode_weighted (lower : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ)
    (field : annularFluxWeakGraph lower positive) (grade : HasAnnularFluxGrade lower positive angular cell inserted field) :
    annularFluxGraphDecode lower positive angular cell inserted
      (annularFluxGraphWeighted lower positive angular cell inserted field grade) = field := by
  apply Subtype.ext
  apply Prod.ext
  · exact annularLpDecode_weighted angular cell inserted field.val.1 grade.1
  · exact annularLpDecode_weighted angular cell inserted field.val.2 grade.2

theorem annularFluxGraphDecode_injective (lower : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ) :
    Function.Injective (annularFluxGraphDecode lower positive angular cell inserted) := by
  intro first second same
  apply Subtype.ext
  apply Prod.ext
  · apply annularLpDecode_injective angular cell inserted
    exact congrArg (fun field : annularFluxWeakGraph lower positive => field.val.1) same
  · apply annularLpDecode_injective angular cell inserted
    exact congrArg (fun field : annularFluxWeakGraph lower positive => field.val.2) same

section Actual
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) (angular cell inserted : ℕ)

theorem annularSolvedFlux_decoded_weighted (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data) :
    annularFluxGraphDecode lower positive angular cell inserted
      (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength
        (annularWeightedData lower angular cell inserted data grade)) =
      annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength data :=
  (annularSolvedFlux_diagonal parameters lower length positive bounded lengthPositive widthHalf widthLength
    (fun mode => (annularGradeWeight angular cell inserted mode)⁻¹) 1 (by norm_num)
    (annularGradeWeight_inv_bound angular cell inserted) (annularWeightedData lower angular cell inserted data grade)).trans
      (congrArg (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength)
        (annularDataDecode_weighted lower angular cell inserted data grade))

theorem annularSolvedFlux_hasGrade (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data) :
    HasAnnularFluxGrade lower positive angular cell inserted
      (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength data) :=
  (congrArg (HasAnnularFluxGrade lower positive angular cell inserted)
    (annularSolvedFlux_decoded_weighted parameters lower length positive bounded lengthPositive widthHalf widthLength
      angular cell inserted data grade)).mp
        (annularFluxGraphDecode_hasGrade lower positive angular cell inserted
          (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength
            (annularWeightedData lower angular cell inserted data grade)))

theorem annularSolvedFlux_weighted_identity (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data)
    (fluxGrade : HasAnnularFluxGrade lower positive angular cell inserted
      (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength data)) :
    annularFluxGraphWeighted lower positive angular cell inserted
      (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength data) fluxGrade =
      annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength
        (annularWeightedData lower angular cell inserted data grade) := by
  apply annularFluxGraphDecode_injective lower positive angular cell inserted
  exact (annularFluxGraphDecode_weighted lower positive angular cell inserted _ fluxGrade).trans
    (annularSolvedFlux_decoded_weighted parameters lower length positive bounded lengthPositive widthHalf widthLength
      angular cell inserted data grade).symm

end Actual
end Grad.AnnularFluxTrace
