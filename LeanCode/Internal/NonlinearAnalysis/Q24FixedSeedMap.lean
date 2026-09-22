import Q24CompletedPolynomial
import TameFixedSliceProof

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped ContDiff

namespace Grad.Q24Realization

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearQuotientBounds
open Grad.Constraints Grad.AxisCore Grad.SmoothingFamily Grad.ImplementationReadiness
open Grad.QuotientProjection

/-- Curvature and the original state sum norm. -/
abbrev JointAmbient (parameters : PhaseParameters) (grade : ℕ) :=
  WithLp 1 (ℂ × XAmbient parameters grade)

def jointCoreEmbed (parameters : PhaseParameters) (grade : ℕ) (state : JointState parameters) :
    JointAmbient parameters grade :=
  WithLp.toLp 1 (state.1, chartCoreEmbed parameters grade state.2)

theorem jointCoreEmbed_norm (parameters : PhaseParameters) (grade : ℕ)
    (state : JointState parameters) :
    ‖jointCoreEmbed parameters grade state‖ = jointNorm grade state := by
  rw [jointCoreEmbed, WithLp.prod_norm_eq_of_L1]
  change ‖state.1‖ + ‖chartCoreEmbed parameters grade state.2‖ = _
  rw [chartCoreEmbed_norm]
  rfl

def jointDomain (parameters : PhaseParameters) (grade : ℕ) : Set (JointAmbient parameters grade) :=
  {state | state.ofLp.2 ∈ chartDomain parameters grade}

theorem jointDomain_isOpen (parameters : PhaseParameters) (grade : ℕ) :
    IsOpen (jointDomain parameters grade) :=
  (chartDomain_isOpen parameters grade).preimage
    (WithLp.prodContinuousLinearEquiv 1 ℝ ℂ (XAmbient parameters grade)).continuous.snd

theorem jointDomain_core_iff (parameters : PhaseParameters) (grade : ℕ)
    (state : JointState parameters) :
    jointCoreEmbed parameters grade state ∈ jointDomain parameters grade ↔ ChartAxisCondition state.2 :=
  axisDomain_core_iff parameters grade state.2.1

def completedReferenceState (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (state : JointAmbient parameters grade) : PolynomialState parameters grade :=
  let fields := completedChart parameters seed insideS grade
    (completedReferenceTransfer parameters reference insideR seed insideS grade state.ofLp.2)
  statePack state.ofLp.1 fields.1 fields.2

theorem completedReferenceState_contDiffOn (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedReferenceState parameters reference insideR seed insideS grade)
      (jointDomain parameters grade) := by
  have pairSmooth : ContDiff ℝ ∞ (fun state : JointAmbient parameters grade => state.ofLp) :=
    (WithLp.prodContinuousLinearEquiv 1 ℝ ℂ (XAmbient parameters grade)).contDiff
  have transferred := (completedReferenceTransfer_contDiff parameters reference insideR seed insideS grade).comp
    pairSmooth.snd
  have chartSmooth := (completedChart_contDiffOn parameters seed insideS grade).comp
    transferred.contDiffOn (fun _ membership => membership)
  have fieldsSmooth := (WithLp.prodContinuousLinearEquiv 1 ℝ
    (AGrade parameters 3 grade) (AGrade parameters 1 grade)).symm.contDiff.comp_contDiffOn chartSmooth
  exact (WithLp.prodContinuousLinearEquiv 1 ℝ ℂ
    (WithLp 1 (AGrade parameters 3 grade × AGrade parameters 1 grade))).symm.contDiff.comp_contDiffOn
      (pairSmooth.fst.contDiffOn.prodMk fieldsSmooth)

theorem completedReferenceState_core (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (state : JointState parameters) (axis : ChartAxisCondition state.2) :
    completedReferenceState parameters reference insideR seed insideS grade
      (jointCoreEmbed parameters grade state) =
      polynomialStateEmbed parameters grade (referenceState parameters reference insideR seed insideS state) := by
  unfold completedReferenceState jointCoreEmbed
  rw [WithLp.ofLp_toLp, completedReferenceTransfer_core,
    completedChart_core parameters seed insideS grade
      (referenceTransfer parameters reference insideR seed insideS state.2)
      (show ChartAxisCondition (referenceTransfer parameters reference insideR seed insideS state.2) from axis)]
  rfl

/-- Fixed-seed Q21 on the genuine Banach carriers, before proving the
constrained-range and finite-seed-parameter clauses of the full Q24 boundary. -/
def completedFixedSlice (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (state : JointAmbient parameters (grade + 6)) : ZAmbient parameters grade :=
  completedPolynomial parameters cellLength grade
    (completedReferenceState parameters reference insideR seed insideS (grade + 6) state)

theorem completedFixedSlice_contDiffOn (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedFixedSlice parameters cellLength reference insideR seed insideS grade)
      (jointDomain parameters (grade + 6)) :=
  (completedPolynomial_contDiff parameters cellLength grade).comp_contDiffOn
    (completedReferenceState_contDiffOn parameters reference insideR seed insideS (grade + 6))

theorem completedFixedSlice_core (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (state : JointState parameters) (axis : ChartAxisCondition state.2) :
    completedFixedSlice parameters cellLength reference insideR seed insideS grade
      (jointCoreEmbed parameters (grade + 6) state) =
      quotientEta parameters grade (fixedSliceMap parameters cellLength reference insideR seed insideS state) := by
  rw [completedFixedSlice, completedReferenceState_core parameters reference insideR seed insideS _ state axis,
    completedPolynomial_core]
  rfl

end Grad.Q24Realization
