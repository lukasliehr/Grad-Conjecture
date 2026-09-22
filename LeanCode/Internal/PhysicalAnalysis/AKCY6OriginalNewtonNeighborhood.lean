import AKCY5ShiftedOriginalAnalyticBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500
open Set

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.SmoothingFamily Grad.Q24Realization Grad.NashMoser.OriginalLimit Grad.SmoothForward
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates

attribute [local irreducible] originalNonlinearSource literalPhysicalSmoothForward
  originalLiteralTaylorRemainder stateSize sourceSize

variable (parameters : PhaseParameters) (reference : Seed.Parameters)
    (inside : reference ∈ Seed.parameterDomain)

/-- The one original PC parameter product used throughout the iteration.
Only the low grade is bounded; arbitrary higher state norms remain free. -/
structure OriginalNewtonNeighborhood (base : ℕ) where
  baseLarge : 4 ≤ base
  parameterDomain : Set OriginalFiniteParameter
  seedPatch : Set Seed.Parameters
  compact : IsCompact seedPatch
  patchInside : seedPatch ⊆ Seed.parameterDomain
  curvatureBound : ℝ
  seedInside : ∀ finite ∈ parameterDomain, finite.1 ∈ seedPatch
  curvature : ∀ finite ∈ parameterDomain, ‖finite.2‖ ≤ curvatureBound
  radius : ℝ
  radiusPositive : 0 < radius
  radiusSmall : radius ≤ 1
  axis : ∀ state : stateSmoothRange parameters reference inside,
    stateSize parameters reference inside base 0 state ≤ 2*radius →
    ChartAxisCondition (smoothingChartCore parameters state.val)

variable {parameters reference inside}

namespace OriginalNewtonNeighborhood
variable {base : ℕ} (neighborhood : OriginalNewtonNeighborhood parameters reference inside base)
    (cellLength : ℝ) (loss : ℕ) (lossLarge : 6 ≤ loss)

/-- Constants are selected from the actual QYP estimates, before any stage,
time, or high norm is introduced. -/
def residualConstant (grade : ℕ) : ℝ :=
  (originalResidual_shifted parameters reference inside cellLength base loss neighborhood.baseLarge lossLarge
    neighborhood.seedPatch neighborhood.compact neighborhood.patchInside neighborhood.curvatureBound
      (2*neighborhood.radius) grade).choose

def forwardConstant (grade : ℕ) : ℝ :=
  (originalForward_shifted parameters reference inside cellLength base loss neighborhood.baseLarge lossLarge
    neighborhood.seedPatch neighborhood.compact neighborhood.patchInside neighborhood.curvatureBound
      (2*neighborhood.radius) grade).choose

def taylorConstant (grade : ℕ) : ℝ :=
  (originalStateTaylor_shifted parameters reference inside cellLength base loss neighborhood.baseLarge lossLarge
    neighborhood.seedPatch neighborhood.compact neighborhood.patchInside neighborhood.curvatureBound
      (2*neighborhood.radius) grade).choose

theorem residualConstant_nonnegative (grade : ℕ) :
    0 ≤ neighborhood.residualConstant cellLength loss lossLarge grade :=
  (originalResidual_shifted parameters reference inside cellLength base loss neighborhood.baseLarge lossLarge
    neighborhood.seedPatch neighborhood.compact neighborhood.patchInside neighborhood.curvatureBound
      (2*neighborhood.radius) grade).choose_spec.1

theorem forwardConstant_nonnegative (grade : ℕ) :
    0 ≤ neighborhood.forwardConstant cellLength loss lossLarge grade :=
  (originalForward_shifted parameters reference inside cellLength base loss neighborhood.baseLarge lossLarge
    neighborhood.seedPatch neighborhood.compact neighborhood.patchInside neighborhood.curvatureBound
      (2*neighborhood.radius) grade).choose_spec.1

theorem taylorConstant_nonnegative (grade : ℕ) :
    0 ≤ neighborhood.taylorConstant cellLength loss lossLarge grade :=
  (originalStateTaylor_shifted parameters reference inside cellLength base loss neighborhood.baseLarge lossLarge
    neighborhood.seedPatch neighborhood.compact neighborhood.patchInside neighborhood.curvatureBound
      (2*neighborhood.radius) grade).choose_spec.1

theorem residual_bound (grade : ℕ) (finite : OriginalFiniteParameter)
    (member : finite ∈ neighborhood.parameterDomain) (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside base 0 state ≤ 2*neighborhood.radius) :
    sourceSize parameters base grade
      (originalNonlinearSource parameters cellLength reference inside finite state) ≤
    neighborhood.residualConstant cellLength loss lossLarge grade *
      (1+stateSize parameters reference inside base (grade+loss) state) :=
  (originalResidual_shifted parameters reference inside cellLength base loss neighborhood.baseLarge lossLarge
    neighborhood.seedPatch neighborhood.compact neighborhood.patchInside neighborhood.curvatureBound
      (2*neighborhood.radius) grade).choose_spec.2 finite state (neighborhood.seedInside finite member)
        (neighborhood.curvature finite member) (neighborhood.axis state low) low

theorem forward_bound (grade : ℕ) (finite : OriginalFiniteParameter)
    (member : finite ∈ neighborhood.parameterDomain) (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside base 0 state ≤ 2*neighborhood.radius)
    (direction : stateSmoothRange parameters reference inside) :
    sourceSize parameters base grade
      (literalPhysicalSmoothForward parameters cellLength reference inside finite.1
        (neighborhood.patchInside (neighborhood.seedInside finite member)) (finite.2,state)
        (neighborhood.axis state low) direction) ≤
    neighborhood.forwardConstant cellLength loss lossLarge grade *
      ((1+stateSize parameters reference inside base (grade+loss) state) *
        stateSize parameters reference inside base 0 direction +
        stateSize parameters reference inside base (grade+loss) direction) :=
  (originalForward_shifted parameters reference inside cellLength base loss neighborhood.baseLarge lossLarge
    neighborhood.seedPatch neighborhood.compact neighborhood.patchInside neighborhood.curvatureBound
      (2*neighborhood.radius) grade).choose_spec.2 finite state (neighborhood.seedInside finite member)
        (neighborhood.axis state low) (neighborhood.curvature finite member) low direction

theorem taylor_bound (grade : ℕ) (finite : OriginalFiniteParameter)
    (member : finite ∈ neighborhood.parameterDomain) (state direction : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside base 0 state ≤ 2*neighborhood.radius)
    (highBound : ℝ)
    (segment : ∀ t ∈ Icc (0:ℝ) 1,
      stateSize parameters reference inside base 0 (state+t•direction) ≤ 2*neighborhood.radius ∧
      stateSize parameters reference inside base (grade+loss) (state+t•direction) ≤ highBound) :
    sourceSize parameters base grade
      (originalLiteralTaylorRemainder parameters cellLength reference inside (finite.1,finite.2,state)
        (neighborhood.patchInside (neighborhood.seedInside finite member)) (neighborhood.axis state low)
        (finite.1,finite.2,state+direction)) ≤
    neighborhood.taylorConstant cellLength loss lossLarge grade *
      ((1+highBound) * (stateSize parameters reference inside base 0 direction)^2 +
        2*stateSize parameters reference inside base (grade+loss) direction *
          stateSize parameters reference inside base 0 direction) :=
  (originalStateTaylor_shifted parameters reference inside cellLength base loss neighborhood.baseLarge lossLarge
    neighborhood.seedPatch neighborhood.compact neighborhood.patchInside neighborhood.curvatureBound
      (2*neighborhood.radius) grade).choose_spec.2 finite state direction (neighborhood.seedInside finite member)
        (neighborhood.axis state low) highBound (neighborhood.curvature finite member)
        (fun t ht => ⟨neighborhood.axis _ (segment t ht).1,(segment t ht).1,(segment t ht).2⟩)

end OriginalNewtonNeighborhood

/-- The remaining actual PC right inverse and its one-high bound. All maps
act on the original real constrained cores; no Newton recurrence is assumed. -/
structure OriginalNewtonInverse {base : ℕ} (neighborhood : OriginalNewtonNeighborhood parameters reference inside base)
    (cellLength : ℝ) (loss : ℕ) where
  map : OriginalFiniteParameter → stateSmoothRange parameters reference inside →
    sourceSmoothRange parameters →ₗ[ℝ] stateSmoothRange parameters reference inside
  constant : ℕ → ℝ
  nonnegative : ∀ grade, 0 ≤ constant grade
  right : ∀ finite (member : finite ∈ neighborhood.parameterDomain) state
    (low : stateSize parameters reference inside base 0 state ≤ 2*neighborhood.radius) source,
    literalPhysicalSmoothForward parameters cellLength reference inside finite.1
      (neighborhood.patchInside (neighborhood.seedInside finite member)) (finite.2,state)
      (neighborhood.axis state low) (map finite state source) = source
  bounded : ∀ grade finite, finite ∈ neighborhood.parameterDomain → ∀ state,
    stateSize parameters reference inside base 0 state ≤ 2*neighborhood.radius → ∀ source,
    stateSize parameters reference inside base grade (map finite state source) ≤
      constant grade * (sourceSize parameters base (grade+loss) source +
        (1+stateSize parameters reference inside base (grade+loss) state) * sourceSize parameters base loss source)

end Grad.NashMoser.OriginalIteration
