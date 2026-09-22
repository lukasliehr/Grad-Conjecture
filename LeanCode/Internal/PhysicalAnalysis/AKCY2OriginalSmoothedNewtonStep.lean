import AKCY1ActualConstrainedSmoothing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3500

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.SmoothingFamily Grad.Q24Realization Grad.NashMoser.OriginalLimit Grad.SmoothForward
open Grad.NashMoser.BranchDerivative Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates

variable (parameters : PhaseParameters) (reference : Seed.Parameters)
    (inside : reference ∈ Seed.parameterDomain)

/-- Reindexing of the literal original state norms, with width unchanged. -/
def stateSize (base grade : ℕ) : Seminorm ℝ (stateSmoothRange parameters reference inside) :=
  stateOriginalSeminorms parameters reference inside (base+grade)

def sourceSize (base grade : ℕ) : Seminorm ℝ (sourceSmoothRange parameters) :=
  sourceOriginalSeminorms parameters (base+grade)

theorem stateSize_mono (base : ℕ) {lower upper : ℕ} (ordered : lower ≤ upper)
    (state : stateSmoothRange parameters reference inside) :
    stateSize parameters reference inside base lower state ≤
      stateSize parameters reference inside base upper state := by
  have bound := xLowering_norm_le parameters (Nat.add_le_add_left ordered base)
    (stateToGrade parameters (base+upper) state.val)
  rw [xLowering_core] at bound
  exact bound

theorem sourceSize_mono (base : ℕ) {lower upper : ℕ} (ordered : lower ≤ upper)
    (source : sourceSmoothRange parameters) :
    sourceSize parameters base lower source ≤ sourceSize parameters base upper source := by
  have bound := zLowering_norm_le parameters (Nat.add_le_add_left ordered base)
    (Grad.QuotientProjection.quotientEta parameters (base+upper) source.val)
  rw [zLowering_core] at bound
  exact bound

def smoothedNewtonCorrection (scale : ℝ)
    (inverse : sourceSmoothRange parameters →ₗ[ℝ] stateSmoothRange parameters reference inside)
    (residual : sourceSmoothRange parameters) : stateSmoothRange parameters reference inside :=
  -originalStateSmoothing parameters reference inside scale (inverse residual)

def smoothedNewtonNext (cellLength : ℝ) (finite : OriginalFiniteParameter)
    (scale : ℝ) (state : stateSmoothRange parameters reference inside)
    (inverse : sourceSmoothRange parameters →ₗ[ℝ] stateSmoothRange parameters reference inside) :
    stateSmoothRange parameters reference inside :=
  state + smoothedNewtonCorrection parameters reference inside scale inverse
    (originalNonlinearSource parameters cellLength reference inside finite state)

theorem smoothedNewtonCorrection_norm_le (base grade : ℕ) (large : 3 ≤ base)
    (scale : ℝ) (positive : 0 < scale)
    (inverse : sourceSmoothRange parameters →ₗ[ℝ] stateSmoothRange parameters reference inside)
    (residual : sourceSmoothRange parameters) :
    stateSize parameters reference inside base grade
      (smoothedNewtonCorrection parameters reference inside scale inverse residual) ≤
      originalSmoothingGain parameters reference inside base (base+grade) * scale ^ grade *
        stateSize parameters reference inside base 0 (inverse residual) := by
  change ‖stateToGrade parameters (base+grade)
    (-(originalStateSmoothing parameters reference inside scale (inverse residual)).val)‖ ≤ _
  rw [map_neg, norm_neg]
  have bound := originalStateSmoothing_norm_le parameters reference inside scale positive
    base (base+grade) (Nat.le_add_right _ _) (large.trans (Nat.le_add_right _ _)) (inverse residual)
  simpa only [Nat.add_sub_cancel_left, stateSize, stateOriginalSeminorms_apply, Nat.add_zero] using bound

/-- Internal real-linear identity; no analytic assertion is encoded here. -/
theorem smoothedCoreStep_identity {Parameter State Source : Type*}
    [AddCommGroup Parameter] [Module ℝ Parameter]
    [AddCommGroup State] [Module ℝ State] [AddCommGroup Source] [Module ℝ Source]
    (mapping : Parameter → State → Source) (parameter : Parameter) (state : State)
    (forward : State →ₗ[ℝ] Source) (parameterDerivative : Parameter →ₗ[ℝ] Source)
    (inverse : Source →ₗ[ℝ] State) (smoothing : State →ₗ[ℝ] State)
    (right : forward (inverse (mapping parameter state)) = mapping parameter state) :
    mapping parameter (state + -smoothing (inverse (mapping parameter state))) =
      forward (inverse (mapping parameter state)-smoothing (inverse (mapping parameter state)))+
      coreTaylorRemainder mapping parameter parameter state
        (state + -smoothing (inverse (mapping parameter state))) parameterDerivative forward := by
  simp only [coreTaylorRemainder, sub_self, map_zero, sub_zero, map_sub, map_add, map_neg, right]
  abel

attribute [local irreducible] originalNonlinearSource literalPhysicalSmoothForward
  originalParameterDerivative originalStateSmoothing

/-- Exact original NM07 residual identity. The right inverse is used only on
this actual source; the smoothing defect remains in the SAME full state. -/
theorem smoothedNewton_residual_identity (cellLength : ℝ)
    (finite : OriginalFiniteParameter) (seedInside : finite.1 ∈ Seed.parameterDomain)
    (scale : ℝ) (state : stateSmoothRange parameters reference inside)
    (axis : ChartAxisCondition (smoothingChartCore parameters state.val))
    (inverse : sourceSmoothRange parameters →ₗ[ℝ] stateSmoothRange parameters reference inside)
    (rightInverse : literalPhysicalSmoothForward parameters cellLength reference inside finite.1 seedInside
      (finite.2,state) axis
      (inverse (originalNonlinearSource parameters cellLength reference inside finite state)) =
        originalNonlinearSource parameters cellLength reference inside finite state) :
    originalNonlinearSource parameters cellLength reference inside finite
      (smoothedNewtonNext parameters reference inside cellLength finite scale state inverse) =
    literalPhysicalSmoothForward parameters cellLength reference inside finite.1 seedInside (finite.2,state) axis
      (inverse (originalNonlinearSource parameters cellLength reference inside finite state) -
        originalStateSmoothing parameters reference inside scale
          (inverse (originalNonlinearSource parameters cellLength reference inside finite state))) +
      originalLiteralTaylorRemainder parameters cellLength reference inside (finite.1,finite.2,state)
        seedInside axis (finite.1,finite.2,
          smoothedNewtonNext parameters reference inside cellLength finite scale state inverse) := by
  exact smoothedCoreStep_identity
    (originalNonlinearSource parameters cellLength reference inside) finite state
    (literalPhysicalSmoothForward parameters cellLength reference inside finite.1 seedInside (finite.2,state) axis)
    (originalParameterDerivative parameters reference inside cellLength (finite.1,finite.2,state) seedInside axis)
    inverse (originalStateSmoothing parameters reference inside scale) rightInverse

end Grad.NashMoser.OriginalIteration
