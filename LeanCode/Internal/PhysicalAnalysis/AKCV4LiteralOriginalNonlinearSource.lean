import AKCV3ExactZeroBranchSmoothness
import QYP24PhysicalMixedConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3500

namespace Grad.NashMoser.OriginalLimit
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.QuotientProjection
open Grad.Q24Realization Grad.PhysicalCoordinates Grad.NonlinearQuotientBounds

/-- Original finite coordinates: all four real seed parameters and curvature. -/
abbrev OriginalFiniteParameter := Seed.Parameters × ℝ

/-- The literal physical nonlinear source on its original admissible domain.
The zero value outside that domain only makes a total function for ordinary
Banach calculus; the next theorem identifies every admissible value without
inserting a target projection. -/
def originalNonlinearSource (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (finite : OriginalFiniteParameter) (state : stateSmoothRange parameters reference insideR) :
    sourceSmoothRange parameters := by
  classical
  exact if insideS : finite.1 ∈ Seed.parameterDomain then
    if axis : ChartAxisCondition (smoothingChartCore parameters state.val) then
      ⟨physicalFixedSliceMap parameters cellLength reference insideR finite.1 insideS
        ((finite.2 : ℂ), smoothingChartCore parameters state.val),
        physicalFixedSliceMap_constrained_mem parameters cellLength finite.2 reference insideR finite.1 insideS state axis⟩
    else 0
  else 0

theorem originalNonlinearSource_value (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (finite : OriginalFiniteParameter) (state : stateSmoothRange parameters reference insideR)
    (insideS : finite.1 ∈ Seed.parameterDomain)
    (axis : ChartAxisCondition (smoothingChartCore parameters state.val)) :
    (originalNonlinearSource parameters cellLength reference insideR finite state).val =
      physicalFixedSliceMap parameters cellLength reference insideR finite.1 insideS
        ((finite.2 : ℂ), smoothingChartCore parameters state.val) := by
  simp only [originalNonlinearSource, dif_pos insideS, dif_pos axis]

/-- Agreement with the accepted original real Q24 Banach realization,
including the original six-grade input shift and actual constrained source. -/
theorem originalNonlinearSource_completed (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (finite : OriginalFiniteParameter) (state : stateSmoothRange parameters reference insideR)
    (insideS : finite.1 ∈ Seed.parameterDomain)
    (axis : ChartAxisCondition (smoothingChartCore parameters state.val))
    (grade : ℕ) (large : 3 ≤ grade) :
    sourceSmoothEmbedding parameters grade large
      (originalNonlinearSource parameters cellLength reference insideR finite state) =
      completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large
        (realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade)
          (finite.1, finite.2, state)) := by
  apply Subtype.ext
  change quotientEta parameters grade
    (originalNonlinearSource parameters cellLength reference insideR finite state).val = _
  rw [originalNonlinearSource_value parameters cellLength reference insideR finite state insideS axis]
  exact (completedRealPhysicalMixedSlice_core parameters cellLength reference insideR grade large
    (finite.1, finite.2, state) insideS axis).symm

/-- The original core embedding is real linear, with no norm assigned to
the all-grade core. This explicit map is the SAME accepted Q24 embedding. -/
def originalMixedCoreEmbedding (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    RealMixedCore parameters reference insideR →ₗ[ℝ]
      RealMixedAmbient parameters reference insideR grade large :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1
    (RealJointAmbient parameters reference insideR grade large)).symm.toLinearMap.comp
      (seedL1Equiv.symm.toLinearMap.prodMap
        ((WithLp.prodContinuousLinearEquiv 1 ℝ ℝ
          (stateRange parameters reference insideR grade large)).symm.toLinearMap.comp
            ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap
              (stateSmoothEmbedding parameters reference insideR grade large))))

theorem originalMixedCoreEmbedding_apply (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealMixedCore parameters reference insideR) :
    originalMixedCoreEmbedding parameters reference insideR grade large state =
      realMixedCoreEmbed parameters reference insideR grade large state := rfl

end Grad.NashMoser.OriginalLimit
