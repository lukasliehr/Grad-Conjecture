import AAZJ14ClosedJointPhysicalJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularJointRegularity
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularRadialJets Grad.AnnularRegularity

/-- The SAME actual variational inverse reconstructs to joint smooth physical
p and xi. All mixed physical derivatives extend continuously to both original
radial endpoints, differentiate term by term, and recover the original
phase-decoded L² fields under the actual Fourier integrals. Only source jets
and the prescribed data have regularity hypotheses. -/
theorem annularOriginal_jointSmoothPhysicalReconstruction (parameters : PhaseParameters) (lower length : ℝ)
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
    let weak := annularOriginalStateJet_weak parameters lower length positive bounded lengthPositive widthHalf widthLength
      source innerValue sourceJet sourceZero sourceWeak
    let grades := annularOriginalStateJet_allGrades parameters lower length positive bounded lengthPositive widthHalf widthLength
      source innerValue sourceJet dataGrades sourceGrades
    AnnularJointPhysicalRealization parameters lower positive bounded (fun order => (jet order).1)
      (fun order => (weak order).1) (fun order grade => (grades order grade).1) ∧
    AnnularJointPhysicalRealization parameters lower positive bounded (fun order => (jet order).2)
      (fun order => (weak order).2) (fun order grade => (grades order grade).2) := by
  dsimp only
  constructor <;> exact annularPhysicalJets_jointRealization parameters lower positive bounded _ _ _

end Grad.AnnularJointRegularity
