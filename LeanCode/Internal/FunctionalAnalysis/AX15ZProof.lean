import AX14ZInterface

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.AxisCore

open Grad.ClosedJets Grad.CartesianState

/-- The actual COR20 fourfold quotient ambient theorem. -/
theorem actualQuotientAmbient : QuotientAmbientGoal := by
  intro parameters grade
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun element => zAmbient_norm_sq parameters grade element
  · exact zAmbient_completeSpace parameters grade
  · exact zAmbient_innerProductSpace parameters grade
  · exact fun cores =>
      ⟨fun coordinate => zEmbedding_apply parameters grade cores coordinate,
        zEmbedding_norm_sq parameters grade cores⟩
  · exact zEmbedding_denseRange parameters grade
  · exact fun planar third fourth => zSpinPack_norm_sq parameters grade planar third fourth

end Grad.AxisCore
