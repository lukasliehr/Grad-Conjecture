import AKCV4LiteralOriginalNonlinearSource

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3500
open scoped ContDiff

namespace Grad.NashMoser.OriginalLimit
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.QuotientProjection
open Grad.Q24Realization Grad.PhysicalCoordinates Grad.NonlinearQuotientBounds

variable (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (base : RealMixedCore parameters reference insideR) (insideS : base.1 ∈ Seed.parameterDomain)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.2.val))

/-- The literal first member of the already checked physical mixed tower,
in the original smooth real source. -/
def originalMixedDerivativeValue (direction : RealMixedCore parameters reference insideR) :
    sourceSmoothRange parameters :=
  ⟨physicalMixedSliceCoreTower parameters cellLength reference insideR 1
      (base.1, realJointCoreToJoint parameters reference insideR base.2)
      (fun _ => (direction.1, realJointCoreToJoint parameters reference insideR direction.2)),
    physicalMixedSliceCoreTower_constrained_mem parameters cellLength reference insideR 1
      base insideS axis (fun _ => direction)⟩

theorem originalMixedDerivativeValue_completed
    (grade : ℕ) (large : 3 ≤ grade) (direction : RealMixedCore parameters reference insideR) :
    sourceSmoothEmbedding parameters grade large
      (originalMixedDerivativeValue parameters cellLength reference insideR base insideS axis direction) =
      ((fderiv ℝ (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large)
        (realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade) base)).toLinearMap.comp
        (originalMixedCoreEmbedding parameters reference insideR (grade+6) (realHighLarge grade))) direction := by
  apply Subtype.ext
  have same := completedRealPhysicalMixedSlice_derivative_core parameters cellLength reference insideR
    grade large 1 base insideS axis (fun _ => direction)
  rw [iteratedFDeriv_one_apply] at same
  exact same.symm

/-- The actual mixed smooth-core derivative is linear because its faithful
completed realizations are the actual Frechet derivatives of Q24. -/
def originalMixedDerivative : RealMixedCore parameters reference insideR →ₗ[ℝ] sourceSmoothRange parameters where
  toFun := originalMixedDerivativeValue parameters cellLength reference insideR base insideS axis
  map_add' first second := by
    apply sourceSmoothEmbedding_injective parameters 4 (by omega)
    rw [map_add, originalMixedDerivativeValue_completed, originalMixedDerivativeValue_completed,
      originalMixedDerivativeValue_completed, map_add]
  map_smul' scalar direction := by
    apply sourceSmoothEmbedding_injective parameters 4 (by omega)
    rw [map_smul, originalMixedDerivativeValue_completed, originalMixedDerivativeValue_completed, map_smul]
    rfl

theorem originalMixedDerivative_completed
    (grade : ℕ) (large : 3 ≤ grade) (direction : RealMixedCore parameters reference insideR) :
    sourceSmoothEmbedding parameters grade large
      (originalMixedDerivative parameters cellLength reference insideR base insideS axis direction) =
      (fderiv ℝ (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large)
        (realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade) base))
          (realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade) direction) :=
  originalMixedDerivativeValue_completed parameters cellLength reference insideR base insideS axis grade large direction

end Grad.NashMoser.OriginalLimit
