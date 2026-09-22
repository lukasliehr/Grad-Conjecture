import AAZ17OriginalFiniteRadialRecurrence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRadialJets
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace









/-- Exact AG34 consumer for the SAME actual variational inverse: genuine
physical weak derivatives, actual finite weighted membership, and the
uniform finite-order norm recurrence. The only regularity hypotheses are
on the prescribed physical source jets and the two boundary data. -/
theorem annularOriginal_physicalRadialRegularity (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (source : AnnularForcing lower) (innerValue : AnnularBoundary) (sourceJet : ℕ → AnnularRawSource lower)
    (sourceZero : sourceJet 0 = annularOriginalRawSource lower source)
    (sourceWeak : AnnularPhysicalSourceJets parameters lower positive sourceJet)
    (dataGrades : ∀ grade, HasAnnularDataGrade lower 0 0 grade (source, innerValue))
    (sourceGrades : ∀ order grade, HasAnnularRawSourceGrade lower grade (sourceJet order)) :
    let initial := annularOriginalRawState parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
    let jet := annularPhysicalStateJet lower positive length initial sourceJet
    let jetGrades := annularOriginalStateJet_allGrades parameters lower length positive bounded lengthPositive widthHalf widthLength
      source innerValue sourceJet dataGrades sourceGrades
    (∀ order,
      AnnularPhysicalWeakDerivative parameters lower positive (jet order).1 (jet (order + 1)).1 ∧
      AnnularPhysicalWeakDerivative parameters lower positive (jet order).2 (jet (order + 1)).2) ∧
    (∀ order grade, HasAnnularRawStateGrade lower grade (jet order)) ∧
    (∀ order grade,
      annularRawStateSize lower grade (jet (order + 1)) (jetGrades (order + 1) grade) ≤
        annularRadialRecurrenceConstant lower length order *
          (annularJetPrefixSize lower (grade + 2) order jet jetGrades +
           ‖annularRawWeighted lower (grade + 1) (sourceJet order).1 (sourceGrades order (grade + 1)).1‖ +
           ‖annularRawWeighted lower (grade + 1) (sourceJet order).2.1 (sourceGrades order (grade + 1)).2.1‖ +
           ‖annularRawWeighted lower (grade + 1) (sourceJet order).2.2 (sourceGrades order (grade + 1)).2.2‖)) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro order
    exact annularOriginalStateJet_weak parameters lower length positive bounded lengthPositive widthHalf widthLength
      source innerValue sourceJet sourceZero sourceWeak order
  · exact annularOriginalStateJet_allGrades parameters lower length positive bounded lengthPositive widthHalf widthLength
      source innerValue sourceJet dataGrades sourceGrades
  · intro order grade
    exact annularPhysicalStateJet_recurrence lower length positive lengthPositive _ sourceJet
      (annularOriginalStateJet_allGrades parameters lower length positive bounded lengthPositive widthHalf widthLength
        source innerValue sourceJet dataGrades sourceGrades) sourceGrades order grade

/-- Literal norm identification: the state norm in AG34 is the square sum
of nu^t times the actual sqrt(r)e^Phi physical-derivative coordinates. -/
theorem annularPhysicalJetSize_literal (lower : ℝ) (grade : ℕ) (field : AnnularRawState lower)
    (member : HasAnnularRawStateGrade lower grade field) :
    annularRawStateSize lower grade field member ^ 2 =
      (∑' mode : HighAnnularMode, (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ (2 * grade) * ‖field.1 mode‖ ^ 2) +
      (∑' mode : HighAnnularMode, (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ (2 * grade) * ‖field.2 mode‖ ^ 2) := by
  rw [annularRawStateSize_square, annularRawWeighted_norm_sq, annularRawWeighted_norm_sq]

end Grad.AnnularRadialJets
