import AX9AmbientInterface

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.AxisCore

open Grad.ClosedJets Grad.CartesianState

/-- The actual COR17 ambient-product theorem. -/
theorem actualAmbientProduct : AmbientProductGoal := by
  intro parameters grade _
  exact ⟨xAmbient_norm parameters grade, stateToGrade_embedded_norm parameters grade,
    Grad.SmoothingFamily.stateToGrade_injective parameters grade,
    stateToGrade_denseRange parameters grade⟩

end Grad.AxisCore
