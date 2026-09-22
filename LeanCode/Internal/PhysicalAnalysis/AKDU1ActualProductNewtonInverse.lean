import AKDS21OriginalNewtonHigherBase
import AKDE25ActualOriginalCellSolutionFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set

namespace Grad.OriginalMainConsumer
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.Q24Realization
open Grad.PhysicalCoordinates Grad.OriginalCoreRealization Grad.NonlinearQuotientBounds
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit
open Grad.OriginalInverseNeighborhood

variable {parameters : PhaseParameters} {positive : 0 < parameters.length}
  {reference : Seed.Parameters} {inside : reference ∈ Seed.parameterDomain} {center : Seed.Parameters}

/-- The sole remaining analytic bound, on the SAME already constructed
original inverse. The fixed base and fixed loss may be larger than 24 and 6;
the independent low source payment and original width remain unchanged. -/
structure ActualProductOneHigh (product : OriginalPhysicalProduct parameters positive reference inside center)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length))
    (base loss : ℕ) where
  baseLarge : 24 ≤ base
  constant : ℕ → ℝ
  nonnegative : ∀ grade, 0 ≤ constant grade
  bounded : ∀ grade finite, finite ∈ product.neighborhood.parameterDomain →
    ∀ state : stateSmoothRange parameters reference inside,
    stateSize parameters reference inside base 0 state ≤ 2*product.neighborhood.radius →
    ∀ source : sourceSmoothRange parameters,
      stateSize parameters reference inside base grade
        (product.inverseMap widthHalf widthLength finite state source) ≤
      constant grade * (sourceSize parameters base (grade+loss) source +
        (1+stateSize parameters reference inside base (grade+loss) state) * sourceSize parameters base loss source)

namespace ActualProductOneHigh
variable {product : OriginalPhysicalProduct parameters positive reference inside center}
  {widthHalf : parameters.gamma ≤ 1/2} {widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length)}
  {base loss : ℕ} (estimate : ActualProductOneHigh product widthHalf widthLength base loss)

/-- The actual Newton inverse is obtained by reusing the original map and
its proved right identity; only its displayed one-high bound is supplied. -/
def toNewtonInverse : OriginalNewtonInverse (product.neighborhood.raiseBase base estimate.baseLarge) parameters.length loss where
  map := product.inverseMap widthHalf widthLength
  constant := estimate.constant
  nonnegative := estimate.nonnegative
  right := product.inverseMap_higher_right widthHalf widthLength base estimate.baseLarge
  bounded := estimate.bounded

/-- The SAME map's left identity is already proved for every raised base.
No injectivity or smooth-inverse premise is introduced in the final consumer. -/
theorem toNewtonInverse_leftLaw : estimate.toNewtonInverse.LeftLaw :=
  ⟨product.inverseMap_higher_left widthHalf widthLength base estimate.baseLarge⟩

end ActualProductOneHigh
end Grad.OriginalMainConsumer
