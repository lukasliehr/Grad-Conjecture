import RootUnitIdentity
import RootUnitTower

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! FA-nonlinear-root, assembled: the literal chart root is the Q7/Q8
series on the Q13 ball, it is pointwise the positive square root
`√(1 - |τ(ζ)|²/2)` for real planar families there (Q14), and its derivative
tower is genuine in every graded envelope with the exact one-high Q15
estimates at every order. -/

/-- FA-nonlinear-root: the root unit goal holds. -/
theorem actualRootUnit : RootUnitGoal := by
  intro parameters
  refine ⟨?_, ?_, rootDerivativeFamily, ?_, ?_, ?_⟩
  · intro family axis cell
    exact rootChart_hasSum (rootAxis_quadratic_small axis) cell
  · intro family real axis zeta
    exact ⟨rootAxis_planarValue_lt axis zeta, rootChart_value_eq_sqrt real axis zeta⟩
  · intro family
    exact rootDerivativeFamily_zero family (fun position => position.elim0)
  · intro order base directions axis
    exact rootDerivativeFamily_genuine order base directions axis
  · intro grade order
    exact rootDerivativeFamily_bound grade order

end Grad.NonlinearQuotientBounds
