import Q24MixedMap

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

open scoped BigOperators ContDiff

namespace Grad.Q24Realization

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisCore Grad.SmoothingFamily Grad.RealFixedRanges

/-- Literal finite seed sum, real curvature and original constrained state
norm. The underlying real slice is the accepted reference-seed carrier. -/
abbrev RealMixedAmbient (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :=
  WithLp 1 (SeedL1 × RealJointAmbient parameters reference insideR grade large)

def realMixedInclusion (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    RealMixedAmbient parameters reference insideR grade large →L[ℝ] MixedAmbient parameters grade :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1 (JointAmbient parameters grade)).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.id ℝ SeedL1).prodMap (realJointInclusion parameters reference insideR grade large)).comp
      (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1
        (RealJointAmbient parameters reference insideR grade large)).toContinuousLinearMap)

theorem realMixedInclusion_norm (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealMixedAmbient parameters reference insideR grade large) :
    ‖realMixedInclusion parameters reference insideR grade large state‖ = ‖state‖ := by
  rw [WithLp.prod_norm_eq_of_L1 (realMixedInclusion parameters reference insideR grade large state),
    WithLp.prod_norm_eq_of_L1 state]
  change ‖state.ofLp.1‖ + ‖realJointInclusion parameters reference insideR grade large state.ofLp.2‖ = _
  rw [realJointInclusion_norm]
  rfl

def realMixedSeed (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    RealMixedAmbient parameters reference insideR grade large →L[ℝ] Seed.Parameters :=
  (mixedSeed parameters grade).comp (realMixedInclusion parameters reference insideR grade large)

abbrev RealMixedCore (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) :=
  Seed.Parameters × RealJointCore parameters reference insideR

def realMixedCoreEmbed (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealMixedCore parameters reference insideR) :
    RealMixedAmbient parameters reference insideR grade large :=
  WithLp.toLp 1 (WithLp.toLp 1 state.1, realJointCoreEmbed parameters reference insideR grade large state.2)

theorem realMixedCoreEmbed_denseRange (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    DenseRange (realMixedCoreEmbed parameters reference insideR grade large) :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1
    (RealJointAmbient parameters reference insideR grade large)).symm.surjective.denseRange.comp
      (seedL1Equiv.symm.surjective.denseRange.prodMap
        (realJointCoreEmbed_denseRange parameters reference insideR grade large))
      (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1
        (RealJointAmbient parameters reference insideR grade large)).symm.continuous

theorem realMixedInclusion_core (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealMixedCore parameters reference insideR) :
    realMixedInclusion parameters reference insideR grade large
      (realMixedCoreEmbed parameters reference insideR grade large state) =
    mixedCoreEmbed parameters grade (state.1, realJointCoreToJoint parameters reference insideR state.2) := by
  change WithLp.toLp 1 (WithLp.toLp 1 state.1,
    realJointInclusion parameters reference insideR grade large
      (realJointCoreEmbed parameters reference insideR grade large state.2)) = _
  rw [realJointInclusion_core]
  rfl

def realMixedDomain (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    Set (RealMixedAmbient parameters reference insideR grade large) :=
  (realMixedInclusion parameters reference insideR grade large) ⁻¹' mixedDomain parameters grade

theorem realMixedDomain_isOpen (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    IsOpen (realMixedDomain parameters reference insideR grade large) :=
  (mixedDomain_isOpen parameters grade).preimage
    (realMixedInclusion parameters reference insideR grade large).continuous

theorem realMixedDomain_core_iff (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealMixedCore parameters reference insideR) :
    realMixedCoreEmbed parameters reference insideR grade large state ∈
      realMixedDomain parameters reference insideR grade large ↔
    state.1 ∈ Seed.parameterDomain ∧ ChartAxisCondition (smoothingChartCore parameters state.2.2.val) := by
  change realMixedInclusion parameters reference insideR grade large
    (realMixedCoreEmbed parameters reference insideR grade large state) ∈ mixedDomain parameters grade ↔ _
  rw [realMixedInclusion_core, mixedDomain_core_iff]
  rfl

def completedRealMixedSliceAmbient (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ)
    (state : RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) :
    ZAmbient parameters grade :=
  completedMixedSlice parameters cellLength reference grade
    (realMixedInclusion parameters reference insideR (grade + 6) (realHighLarge grade) state)

theorem completedRealMixedSliceAmbient_contDiffOn (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedRealMixedSliceAmbient parameters cellLength reference insideR grade)
      (realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade)) := by
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) := inferInstance
  exact (completedMixedSlice_contDiffOn parameters cellLength reference grade).comp_continuousLinearMap
    (G := RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (realMixedInclusion parameters reference insideR (grade + 6) (realHighLarge grade))

theorem completedRealMixedSliceAmbient_core (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ)
    (state : RealMixedCore parameters reference insideR)
    (insideS : state.1 ∈ Seed.parameterDomain)
    (axis : ChartAxisCondition (smoothingChartCore parameters state.2.2.val)) :
    completedRealMixedSliceAmbient parameters cellLength reference insideR grade
      (realMixedCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) state) =
    Grad.QuotientProjection.quotientEta parameters grade
      (fixedSliceMap parameters cellLength reference insideR state.1 insideS
        (realJointCoreToJoint parameters reference insideR state.2)) := by
  unfold completedRealMixedSliceAmbient
  rw [realMixedInclusion_core]
  exact completedMixedSlice_core parameters cellLength reference insideR grade _ insideS axis

end Grad.Q24Realization
