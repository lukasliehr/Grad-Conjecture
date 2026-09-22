import Q24ActualTransfer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

open scoped ContDiff

namespace Grad.Q24Realization

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.SmoothingFamily Grad.RealFixedRanges Grad.ImplementationReadiness
open Grad.AxisCore

theorem realHighLarge (grade : ℕ) : 3 ≤ grade + 6 := by omega
theorem realLowLarge : 3 ≤ (4 : ℕ) := by decide
theorem realLowLeHigh (grade : ℕ) : 4 ≤ grade + 6 := by omega

/-- The actual real curvature and real constrained reference slice, with
the original sum norm inherited without renorming. -/
abbrev RealJointAmbient (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :=
  WithLp 1 (ℝ × stateRange parameters reference insideR grade large)

def realJointInclusion (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    RealJointAmbient parameters reference insideR grade large →L[ℝ] JointAmbient parameters grade :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ ℂ (XAmbient parameters grade)).symm.toContinuousLinearMap.comp
    ((Complex.ofRealCLM.prodMap (stateInclusion parameters reference insideR grade large)).comp
      (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ
        (stateRange parameters reference insideR grade large)).toContinuousLinearMap)

theorem realJointInclusion_norm (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealJointAmbient parameters reference insideR grade large) :
    ‖realJointInclusion parameters reference insideR grade large state‖ = ‖state‖ := by
  rw [WithLp.prod_norm_eq_of_L1 (realJointInclusion parameters reference insideR grade large state),
    WithLp.prod_norm_eq_of_L1 state]
  change ‖(state.ofLp.1 : ℂ)‖ + ‖state.ofLp.2.val‖ = ‖state.ofLp.1‖ + ‖state.ofLp.2‖
  rw [Complex.norm_real]
  rfl

abbrev RealJointCore (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) :=
  ℝ × stateSmoothRange parameters reference insideR

def smoothingChartCore (parameters : PhaseParameters) (state : StateCore parameters) :
    ChartState parameters :=
  (smoothingToTangent parameters state.1, state.2)

theorem chartCoreEmbed_smoothing (parameters : PhaseParameters) (grade : ℕ)
    (state : StateCore parameters) :
    chartCoreEmbed parameters grade (smoothingChartCore parameters state) =
      stateToGrade parameters grade state := by
  change statePack (tangentToGrade parameters (grade + 1) (smoothingToTangent parameters state.1))
    (fieldEmbed parameters 3 grade state.2.1) (fieldEmbed parameters 1 grade state.2.2) = _
  rw [tangentToGrade_smoothing]
  rfl

def realJointCoreToJoint (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain)
    (state : RealJointCore parameters reference insideR) : JointState parameters :=
  ((state.1 : ℂ), smoothingChartCore parameters state.2.val)

def realJointCoreEmbed (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealJointCore parameters reference insideR) :
    RealJointAmbient parameters reference insideR grade large :=
  WithLp.toLp 1 (state.1, stateSmoothEmbedding parameters reference insideR grade large state.2)

theorem realJointCoreEmbed_denseRange (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    DenseRange (realJointCoreEmbed parameters reference insideR grade large) :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ
    (stateRange parameters reference insideR grade large)).symm.surjective.denseRange.comp
      (denseRange_id.prodMap (stateSmoothEmbedding_denseRange parameters reference insideR grade large))
      (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ
        (stateRange parameters reference insideR grade large)).symm.continuous

theorem realJointInclusion_core (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealJointCore parameters reference insideR) :
    realJointInclusion parameters reference insideR grade large
      (realJointCoreEmbed parameters reference insideR grade large state) =
    jointCoreEmbed parameters grade (realJointCoreToJoint parameters reference insideR state) := by
  change WithLp.toLp 1 ((state.1 : ℂ), stateToGrade parameters grade state.2.val) =
    WithLp.toLp 1 ((state.1 : ℂ), chartCoreEmbed parameters grade (smoothingChartCore parameters state.2.val))
  rw [chartCoreEmbed_smoothing]

def realJointDomain (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    Set (RealJointAmbient parameters reference insideR grade large) :=
  (realJointInclusion parameters reference insideR grade large) ⁻¹' jointDomain parameters grade

theorem realJointDomain_isOpen (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    IsOpen (realJointDomain parameters reference insideR grade large) :=
  (jointDomain_isOpen parameters grade).preimage
    (realJointInclusion parameters reference insideR grade large).continuous

theorem realJointDomain_core_iff (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealJointCore parameters reference insideR) :
    realJointCoreEmbed parameters reference insideR grade large state ∈
      realJointDomain parameters reference insideR grade large ↔
    ChartAxisCondition (smoothingChartCore parameters state.2.val) := by
  change realJointInclusion parameters reference insideR grade large
    (realJointCoreEmbed parameters reference insideR grade large state) ∈ jointDomain parameters grade ↔ _
  rw [realJointInclusion_core, jointDomain_core_iff]
  rfl

/-- The literal ambient quotient restricted to its actual real reference
slice. The subsequent range proof must establish membership without
modifying this expression by a target projection. -/
def completedRealFixedSliceAmbient (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (state : RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) :
    ZAmbient parameters grade :=
  completedFixedSlice parameters cellLength reference insideR seed insideS grade
    (realJointInclusion parameters reference insideR (grade + 6) (realHighLarge grade) state)

theorem completedRealFixedSliceAmbient_contDiffOn (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedRealFixedSliceAmbient parameters cellLength reference insideR seed insideS grade)
      (realJointDomain parameters reference insideR (grade + 6) (realHighLarge grade)) := by
  have large : 3 ≤ grade + 6 := by omega
  let : NormedSpace ℝ (RealJointAmbient parameters reference insideR (grade + 6) large) :=
    inferInstance
  exact (completedFixedSlice_contDiffOn parameters cellLength reference insideR seed insideS grade).comp_continuousLinearMap
      (G := RealJointAmbient parameters reference insideR (grade + 6) large)
      (realJointInclusion parameters reference insideR (grade + 6) large)

theorem completedRealFixedSliceAmbient_core (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (state : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters state.2.val)) :
    completedRealFixedSliceAmbient parameters cellLength reference insideR seed insideS grade
      (realJointCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) state) =
    Grad.QuotientProjection.quotientEta parameters grade
      (fixedSliceMap parameters cellLength reference insideR seed insideS
        (realJointCoreToJoint parameters reference insideR state)) := by
  unfold completedRealFixedSliceAmbient
  rw [realJointInclusion_core]
  exact completedFixedSlice_core parameters cellLength reference insideR seed insideS grade _ axis

end Grad.Q24Realization
