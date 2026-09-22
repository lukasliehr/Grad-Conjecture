import AKCV5OriginalMixedCoreDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3500

namespace Grad.NashMoser.OriginalLimit
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.QuotientProjection
open Grad.Q24Realization Grad.PhysicalCoordinates Grad.NonlinearQuotientBounds Grad.SmoothForward

variable (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain)

def originalFiniteDirection : OriginalFiniteParameter →ₗ[ℝ] RealMixedCore parameters reference insideR :=
  (LinearMap.id : Seed.Parameters →ₗ[ℝ] Seed.Parameters).prodMap
    ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).prod (0 : ℝ →ₗ[ℝ] stateSmoothRange parameters reference insideR))

def originalStateDirection : stateSmoothRange parameters reference insideR →ₗ[ℝ]
    RealMixedCore parameters reference insideR :=
  (0 : stateSmoothRange parameters reference insideR →ₗ[ℝ] Seed.Parameters).prod
    ((0 : stateSmoothRange parameters reference insideR →ₗ[ℝ] ℝ).prod LinearMap.id)

def originalFiniteDirectionCompleted (grade : ℕ) (large : 3 ≤ grade) :
    OriginalFiniteParameter →L[ℝ] RealMixedAmbient parameters reference insideR grade large :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1
    (RealJointAmbient parameters reference insideR grade large)).symm.toContinuousLinearMap.comp
    (((seedL1Equiv.symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.fst ℝ Seed.Parameters ℝ)).prod
      ((WithLp.prodContinuousLinearEquiv 1 ℝ ℝ
        (stateRange parameters reference insideR grade large)).symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.snd ℝ Seed.Parameters ℝ).prod 0)))

theorem originalFiniteDirectionCompleted_core (grade : ℕ) (large : 3 ≤ grade)
    (direction : OriginalFiniteParameter) :
    originalFiniteDirectionCompleted parameters reference insideR grade large direction =
      realMixedCoreEmbed parameters reference insideR grade large
        (originalFiniteDirection parameters reference insideR direction) := by
  change WithLp.toLp 1 (WithLp.toLp 1 direction.1, WithLp.toLp 1 (direction.2, 0)) =
    WithLp.toLp 1 (WithLp.toLp 1 direction.1, WithLp.toLp 1
      (direction.2, stateSmoothEmbedding parameters reference insideR grade large 0))
  rw [map_zero]

variable (cellLength : ℝ) (base : RealMixedCore parameters reference insideR)
    (insideS : base.1 ∈ Seed.parameterDomain)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.2.val))

/-- All original finite seed and curvature directions, with the constrained
state fixed, applied to the literal physical mixed core derivative. -/
def originalParameterDerivative : OriginalFiniteParameter →ₗ[ℝ] sourceSmoothRange parameters :=
  (originalMixedDerivative parameters cellLength reference insideR base insideS axis).comp
    (originalFiniteDirection parameters reference insideR)

theorem originalParameterDerivative_completed (grade : ℕ) (large : 3 ≤ grade)
    (direction : OriginalFiniteParameter) :
    sourceSmoothEmbedding parameters grade large
      (originalParameterDerivative parameters reference insideR cellLength base insideS axis direction) =
      ((fderiv ℝ (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large)
        (realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade) base)).comp
        (originalFiniteDirectionCompleted parameters reference insideR (grade+6) (realHighLarge grade))) direction := by
  change sourceSmoothEmbedding parameters grade large
    (originalMixedDerivative parameters cellLength reference insideR base insideS axis
      (originalFiniteDirection parameters reference insideR direction)) = _
  rw [originalMixedDerivative_completed]
  rw [ContinuousLinearMap.comp_apply, originalFiniteDirectionCompleted_core]

/-- The finite parameter derivative has an actual bounded realization into
each original source grade, with all finite coordinates retained. -/
theorem originalParameterDerivative_bound (grade : ℕ) (large : 3 ≤ grade)
    (direction : OriginalFiniteParameter) :
    ‖sourceSmoothEmbedding parameters grade large
      (originalParameterDerivative parameters reference insideR cellLength base insideS axis direction)‖ ≤
      ‖(fderiv ℝ (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large)
        (realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade) base)).comp
        (originalFiniteDirectionCompleted parameters reference insideR (grade+6) (realHighLarge grade))‖ * ‖direction‖ := by
  rw [originalParameterDerivative_completed]
  exact ContinuousLinearMap.le_opNorm _ _

/-- The state part of the actual mixed derivative is exactly the original
physical forward operator used by the native inverse, with no new PDE premise. -/
theorem originalMixedDerivative_state (direction : stateSmoothRange parameters reference insideR) :
    originalMixedDerivative parameters cellLength reference insideR base insideS axis
      (originalStateDirection parameters reference insideR direction) =
      literalPhysicalSmoothForward parameters cellLength reference insideR base.1 insideS base.2 axis direction := by
  apply sourceSmoothEmbedding_injective parameters 4 (forwardLarge (le_refl 4))
  rw [originalMixedDerivative_completed]
  change _ = sourceSmoothEmbedding parameters 4 (forwardLarge (le_refl 4))
    (literalPhysicalSmoothForwardValue parameters cellLength reference insideR base.1 insideS base.2 axis direction)
  rw [← actualPhysicalSmoothForward_core_value parameters cellLength reference insideR base.1 insideS
    4 (le_refl 4) base.2 axis direction]
  rw [actualPhysicalSmoothForward_mixed parameters cellLength reference insideR base.1 insideS
    4 (le_refl 4) base.2 axis]
  rfl

theorem originalMixedDerivative_split (finite : OriginalFiniteParameter)
    (direction : stateSmoothRange parameters reference insideR) :
    originalMixedDerivative parameters cellLength reference insideR base insideS axis
      (originalFiniteDirection parameters reference insideR finite +
        originalStateDirection parameters reference insideR direction) =
      originalParameterDerivative parameters reference insideR cellLength base insideS axis finite +
        literalPhysicalSmoothForward parameters cellLength reference insideR base.1 insideS base.2 axis direction := by
  rw [map_add, originalMixedDerivative_state]
  rfl

end Grad.NashMoser.OriginalLimit
