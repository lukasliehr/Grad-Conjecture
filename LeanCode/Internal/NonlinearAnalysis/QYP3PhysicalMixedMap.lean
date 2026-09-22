import QYP2ChartCoordinates
import PCO2PhysicalChartRange

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 800000

open scoped ContDiff

namespace Grad.PhysicalCoordinates

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.Q24Realization Grad.SmoothingFamily Grad.QuotientProjection Grad.ImplementationReadiness
open Grad.AxisCore

/-- Transfer in the accepted storage coordinates, then interpret the vector
in physical coordinates before applying the unchanged normalized chart. -/
def mixedPhysicalReferencePair (parameters : PhaseParameters) (reference : Seed.Parameters)
    (grade : ℕ) (state : MixedAmbient parameters grade) :
    Seed.Parameters × XAmbient parameters grade :=
  (mixedSeed parameters grade state,
    chartVectorToPhysicalGrade parameters grade (mixedReferencePair parameters reference grade state).2)

theorem mixedPhysicalReferencePair_contDiffOn (parameters : PhaseParameters) (reference : Seed.Parameters)
    (grade : ℕ) :
    ContDiffOn ℝ ∞ (mixedPhysicalReferencePair parameters reference grade) (mixedDomain parameters grade) :=
  (mixedSeed parameters grade).contDiff.contDiffOn.prodMk
    (((chartVectorToPhysicalGrade parameters grade).restrictScalars ℝ).contDiff.comp_contDiffOn
      (mixedReferencePair_contDiffOn parameters reference grade).snd)

theorem mixedPhysicalReferencePair_mem (parameters : PhaseParameters) (reference : Seed.Parameters)
    (grade : ℕ) (state : MixedAmbient parameters grade) (inside : state ∈ mixedDomain parameters grade) :
    mixedPhysicalReferencePair parameters reference grade state ∈ movingChartDomain parameters grade :=
  ⟨inside.1, inside.2⟩

theorem mixedPhysicalReferencePair_core (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (grade : ℕ) (state : Seed.Parameters × JointState parameters)
    (insideS : state.1 ∈ Seed.parameterDomain) :
    mixedPhysicalReferencePair parameters reference grade (mixedCoreEmbed parameters grade state) =
      (state.1, chartCoreEmbed parameters grade
        (physicalChartState parameters (referenceTransfer parameters reference insideR state.1 insideS state.2.2))) := by
  change (state.1, chartVectorToPhysicalGrade parameters grade
    (completedReferenceTransferFamily parameters reference grade (state.1, chartCoreEmbed parameters grade state.2.2))) = _
  rw [completedReferenceTransferFamily_agrees parameters reference insideR state.1 insideS,
    completedReferenceTransfer_core, chartVectorToPhysicalGrade_core]
  rfl

def completedPhysicalMixedReferenceState (parameters : PhaseParameters) (reference : Seed.Parameters)
    (grade : ℕ) (state : MixedAmbient parameters grade) : PolynomialState parameters grade :=
  let fields := completedChartFamily parameters grade (mixedPhysicalReferencePair parameters reference grade state)
  statePack (mixedJoint parameters grade state).ofLp.1 fields.1 fields.2

theorem completedPhysicalMixedReferenceState_contDiffOn (parameters : PhaseParameters)
    (reference : Seed.Parameters) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedPhysicalMixedReferenceState parameters reference grade) (mixedDomain parameters grade) := by
  have curvature : ContDiff ℝ ∞ (fun state : MixedAmbient parameters grade =>
      (mixedJoint parameters grade state).ofLp.1) :=
    (WithLp.prodContinuousLinearEquiv 1 ℝ ℂ (XAmbient parameters grade)).contDiff.fst.comp
      (mixedJoint parameters grade).contDiff
  have chart := (completedChartFamily_contDiffOn parameters grade).comp
    (mixedPhysicalReferencePair_contDiffOn parameters reference grade)
    (mixedPhysicalReferencePair_mem parameters reference grade)
  have fields := (WithLp.prodContinuousLinearEquiv 1 ℝ
    (AGrade parameters 3 grade) (AGrade parameters 1 grade)).symm.contDiff.comp_contDiffOn chart
  exact (WithLp.prodContinuousLinearEquiv 1 ℝ ℂ
    (WithLp 1 (AGrade parameters 3 grade × AGrade parameters 1 grade))).symm.contDiff.comp_contDiffOn
      (curvature.contDiffOn.prodMk fields)

theorem completedPhysicalMixedReferenceState_core (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (grade : ℕ) (state : Seed.Parameters × JointState parameters)
    (insideS : state.1 ∈ Seed.parameterDomain) (axis : ChartAxisCondition state.2.2) :
    completedPhysicalMixedReferenceState parameters reference grade (mixedCoreEmbed parameters grade state) =
      polynomialStateEmbed parameters grade
        (physicalReferenceState parameters reference insideR state.1 insideS state.2) := by
  unfold completedPhysicalMixedReferenceState
  rw [mixedPhysicalReferencePair_core parameters reference insideR grade state insideS,
    completedChartFamily_agrees parameters grade state.1 insideS,
    completedChart_core parameters state.1 insideS grade _ (show
      ChartAxisCondition (physicalChartState parameters
        (referenceTransfer parameters reference insideR state.1 insideS state.2.2)) from axis)]
  rfl

/-- Correct physical mixed residual in the original ambient quotient grade.
There is no post-projection and no change to the Q13 domain or loss six. -/
def completedPhysicalMixedSlice (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (grade : ℕ) (state : MixedAmbient parameters (grade + 6)) :
    ZAmbient parameters grade :=
  completedPolynomial parameters cellLength grade
    (completedPhysicalMixedReferenceState parameters reference (grade + 6) state)

theorem completedPhysicalMixedSlice_contDiffOn (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedPhysicalMixedSlice parameters cellLength reference grade)
      (mixedDomain parameters (grade + 6)) :=
  (completedPolynomial_contDiff parameters cellLength grade).comp_contDiffOn
    (completedPhysicalMixedReferenceState_contDiffOn parameters reference (grade + 6))

theorem completedPhysicalMixedSlice_core (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (grade : ℕ) (state : Seed.Parameters × JointState parameters)
    (insideS : state.1 ∈ Seed.parameterDomain) (axis : ChartAxisCondition state.2.2) :
    completedPhysicalMixedSlice parameters cellLength reference grade (mixedCoreEmbed parameters (grade + 6) state) =
      quotientEta parameters grade (physicalFixedSliceMap parameters cellLength reference insideR state.1 insideS state.2) := by
  rw [completedPhysicalMixedSlice,
    completedPhysicalMixedReferenceState_core parameters reference insideR _ state insideS axis,
    completedPolynomial_core]
  rfl

end Grad.PhysicalCoordinates
