import QR18Goal

noncomputable section

namespace Grad.CompletedReality

open Grad.CartesianState Grad.AxisCore

/-- COR22: both actual completed projections commute with the correct real
involutions, with the original norms, cell reversal and quotient spin swap. -/
theorem actualCompletedReality : CompletedRealityGoal := by
  refine ⟨?_, ?_, actualCompletedStateReality, actualCompletedQuotientReality⟩
  · intro parameters dimension grade
    exact ⟨aGradeConjugation_involutive parameters dimension grade,
      axisInvolution_involutive parameters dimension grade,
      (aGradeConjugation parameters dimension grade).norm_map,
      (axisConjugation parameters dimension grade).norm_map,
      aGradeConjugation_eta parameters dimension grade,
      smoothAxisConjugation_eta parameters dimension grade⟩
  · intro parameters grade
    exact ⟨xConjugation_involutive parameters grade, zConjugation_involutive parameters grade,
      (xConjugation parameters grade).norm_map, (zConjugation parameters grade).norm_map,
      xConjugation_eta parameters grade, zConjugation_quotientEta parameters grade⟩

end Grad.CompletedReality
