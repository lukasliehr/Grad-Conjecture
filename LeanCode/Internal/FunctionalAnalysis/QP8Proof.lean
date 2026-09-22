import QP6AffineBounds
import QP7Goal

noncomputable section

namespace Grad.QuotientProjection

theorem actualSmoothQuotientProjection : SmoothQuotientProjectionGoal := by
  intro parameters
  exact ⟨affineTrace_insertion parameters, modeProjection_affineInsertion parameters,
    affineTrace_modeProjection parameters, quotientProjection_bound parameters,
    quotientProjection_idempotent parameters, quotientProjection_range parameters⟩

end Grad.QuotientProjection
