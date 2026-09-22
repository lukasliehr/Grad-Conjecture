import TameChartBound

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct

/-! Q20, assembled: the chart derivative family witnesses the literal
normalized-chart derivative goal — the zeroth level is the literal Q18
chart, every level differentiates genuinely to the next along the newest
direction on the literal Q13 ball, and every level obeys the exact one-high
`X⁴`/`X^q` estimate. -/

/-- Q20: the normalized chart derivative goal holds. -/
theorem actualNormalizedChartDerivative : NormalizedChartDerivativeGoal := by
  intro parameters seed inside
  refine ⟨chartDerivativeFamily parameters seed inside,
    chartDerivativeFamily_zeroth parameters seed inside,
    chartDerivativeFamily_genuine parameters seed inside, ?_⟩
  intro grade _ order _
  obtain ⟨constant, constant_nonneg, estimate⟩ :=
    chartDerivativeFamily_bound parameters seed inside grade order
  exact ⟨constant, constant_nonneg,
    fun base directions axis _ => estimate base directions axis⟩

end Grad.NonlinearQuotientBounds
