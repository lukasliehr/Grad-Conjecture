import Q24MixedCarriers

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

open scoped ContDiff

namespace Grad.Q24Realization

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisCore Grad.SmoothingFamily Grad.ImplementationReadiness
open Grad.QuotientProjection

def mixedReferencePair (parameters : PhaseParameters) (reference : Seed.Parameters)
    (grade : ℕ) (state : MixedAmbient parameters grade) :
    Seed.Parameters × XAmbient parameters grade :=
  (mixedSeed parameters grade state,
    completedReferenceTransferFamily parameters reference grade (mixedStatePair parameters grade state))

theorem mixedReferencePair_contDiffOn (parameters : PhaseParameters) (reference : Seed.Parameters)
    (grade : ℕ) :
    ContDiffOn ℝ ∞ (mixedReferencePair parameters reference grade) (mixedDomain parameters grade) :=
  (mixedSeed parameters grade).contDiff.contDiffOn.prodMk
    ((completedReferenceTransferFamily_contDiffOn parameters reference grade).comp
      (mixedStatePair_contDiff parameters grade).contDiffOn (fun _ inside => inside.1))

theorem mixedReferencePair_mem (parameters : PhaseParameters) (reference : Seed.Parameters)
    (grade : ℕ) (state : MixedAmbient parameters grade) (inside : state ∈ mixedDomain parameters grade) :
    mixedReferencePair parameters reference grade state ∈ movingChartDomain parameters grade :=
  ⟨inside.1, inside.2⟩

/-- The literal moving-seed Q21 reference chart, including real seed
coordinates and curvature, before evaluating the quotient polynomial. -/
def completedMixedReferenceState (parameters : PhaseParameters) (reference : Seed.Parameters)
    (grade : ℕ) (state : MixedAmbient parameters grade) : PolynomialState parameters grade :=
  let fields := completedChartFamily parameters grade (mixedReferencePair parameters reference grade state)
  statePack (mixedJoint parameters grade state).ofLp.1 fields.1 fields.2

theorem completedMixedReferenceState_contDiffOn (parameters : PhaseParameters) (reference : Seed.Parameters)
    (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedMixedReferenceState parameters reference grade) (mixedDomain parameters grade) := by
  have curvature : ContDiff ℝ ∞ (fun state : MixedAmbient parameters grade =>
      (mixedJoint parameters grade state).ofLp.1) :=
    (WithLp.prodContinuousLinearEquiv 1 ℝ ℂ (XAmbient parameters grade)).contDiff.fst.comp
      (mixedJoint parameters grade).contDiff
  have chart := (completedChartFamily_contDiffOn parameters grade).comp
    (mixedReferencePair_contDiffOn parameters reference grade)
    (mixedReferencePair_mem parameters reference grade)
  have fields := (WithLp.prodContinuousLinearEquiv 1 ℝ
    (AGrade parameters 3 grade) (AGrade parameters 1 grade)).symm.contDiff.comp_contDiffOn chart
  exact (WithLp.prodContinuousLinearEquiv 1 ℝ ℂ
    (WithLp 1 (AGrade parameters 3 grade × AGrade parameters 1 grade))).symm.contDiff.comp_contDiffOn
      (curvature.contDiffOn.prodMk fields)

theorem completedMixedReferenceState_agrees (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (grade : ℕ) (state : MixedAmbient parameters grade)
    (insideS : mixedSeed parameters grade state ∈ Seed.parameterDomain) :
    completedMixedReferenceState parameters reference grade state =
      completedReferenceState parameters reference insideR (mixedSeed parameters grade state) insideS grade
        (mixedJoint parameters grade state) := by
  unfold completedMixedReferenceState mixedReferencePair
  rw [completedChartFamily_agrees parameters grade _ insideS]
  change statePack _
    (completedChart parameters _ insideS grade
      (completedReferenceTransferFamily parameters reference grade
        (mixedSeed parameters grade state, (mixedJoint parameters grade state).ofLp.2))).1
    (completedChart parameters _ insideS grade
      (completedReferenceTransferFamily parameters reference grade
        (mixedSeed parameters grade state, (mixedJoint parameters grade state).ofLp.2))).2 = _
  rw [completedReferenceTransferFamily_agrees parameters reference insideR _ insideS]
  rfl

/-- The actual nonlinear residual on the original mixed seed/curvature/state
Banach carrier. No projection or substitute residual is used. -/
def completedMixedSlice (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (grade : ℕ)
    (state : MixedAmbient parameters (grade + 6)) : ZAmbient parameters grade :=
  completedPolynomial parameters cellLength grade
    (completedMixedReferenceState parameters reference (grade + 6) state)

theorem completedMixedSlice_contDiffOn (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedMixedSlice parameters cellLength reference grade)
      (mixedDomain parameters (grade + 6)) :=
  (completedPolynomial_contDiff parameters cellLength grade).comp_contDiffOn
    (completedMixedReferenceState_contDiffOn parameters reference (grade + 6))

theorem completedMixedSlice_agrees (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (grade : ℕ) (state : MixedAmbient parameters (grade + 6))
    (insideS : mixedSeed parameters (grade + 6) state ∈ Seed.parameterDomain) :
    completedMixedSlice parameters cellLength reference grade state =
      completedFixedSlice parameters cellLength reference insideR
        (mixedSeed parameters (grade + 6) state) insideS grade (mixedJoint parameters (grade + 6) state) := by
  unfold completedMixedSlice
  rw [completedMixedReferenceState_agrees parameters reference insideR _ state insideS]
  rfl

theorem completedMixedSlice_core (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (grade : ℕ) (state : Seed.Parameters × JointState parameters)
    (insideS : state.1 ∈ Seed.parameterDomain) (axis : ChartAxisCondition state.2.2) :
    completedMixedSlice parameters cellLength reference grade
      (mixedCoreEmbed parameters (grade + 6) state) =
      quotientEta parameters grade (fixedSliceMap parameters cellLength reference insideR state.1 insideS state.2) := by
  rw [completedMixedSlice_agrees parameters cellLength reference insideR _ _ insideS]
  exact completedFixedSlice_core parameters cellLength reference insideR state.1 insideS grade state.2 axis

end Grad.Q24Realization
