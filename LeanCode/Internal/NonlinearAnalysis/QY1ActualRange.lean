import Q24RealDerivatives
import QO21ConstrainedConsumer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.Q24Realization

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.RealFixedRanges Grad.SmoothingFamily Grad.AxisCore

theorem smoothingChartCore_eq_stateChart (parameters : PhaseParameters) (state : StateCore parameters) :
    smoothingChartCore parameters state = Grad.NonlinearRange.stateChart parameters state := rfl

/-- O21 on the actual dense real core, with the original Q13 domain. -/
theorem completedRealFixedSliceAmbient_core_mem (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealJointCore parameters reference insideR)
    (inside : realJointCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) state ∈
      realJointDomain parameters reference insideR (grade + 6) (realHighLarge grade)) :
    completedRealFixedSliceAmbient parameters cellLength reference insideR seed insideS grade
      (realJointCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) state) ∈
      sourceRange parameters grade large := by
  have axis := (realJointDomain_core_iff parameters reference insideR (grade + 6)
    (realHighLarge grade) state).1 inside
  rw [completedRealFixedSliceAmbient_core parameters cellLength reference insideR seed insideS grade state axis]
  exact Grad.NonlinearRange.fixedSliceMap_constrained_grade_mem parameters cellLength state.1
    reference insideR seed insideS grade large state.2 axis

/-- The actual completed residual lands in the canonical real compatible
codomain on the entire original open domain. No projection is inserted. -/
theorem completedRealFixedSliceAmbient_mem (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    Set.MapsTo (completedRealFixedSliceAmbient parameters cellLength reference insideR seed insideS grade)
      (realJointDomain parameters reference insideR (grade + 6) (realHighLarge grade))
      (sourceRange parameters grade large) :=
  mapsTo_closed_of_dense_core
    (realJointCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade))
    (realJointCoreEmbed_denseRange parameters reference insideR (grade + 6) (realHighLarge grade))
    _ _ _ (realJointDomain_isOpen parameters reference insideR (grade + 6) (realHighLarge grade))
    (sourceRange_closed parameters grade large)
    (completedRealFixedSliceAmbient_contDiffOn parameters cellLength reference insideR seed insideS grade).continuousOn
    (completedRealFixedSliceAmbient_core_mem parameters cellLength reference insideR seed insideS grade large)

end Grad.Q24Realization
