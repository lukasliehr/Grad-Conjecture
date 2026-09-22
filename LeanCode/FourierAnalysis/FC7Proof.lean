import FC7Interface

noncomputable section

open Filter
open scoped Topology

namespace Grad.CartesianState

theorem cartesianCoreTruncationRealityBlock :
    CartesianCoreTruncationRealityGoal := by
  intro dimension parameters
  refine ⟨?_, tendsto_cartesianCoreTruncation_every_grade parameters,
    cartesianCoreConjugation_involutive parameters, ?_,
    cartesianCoreTruncation_conjugation_commute parameters, ?_⟩
  · intro cutoff field cell
    simp only [cartesianCoreTruncation_apply, mem_centeredCellBox_iff]
  · intro field cell point coordinate
    rw [cartesianCoreConjugation_apply, closedJetConjugate_value_apply]
  · intro grade
    refine ⟨(fun field => (gradeCoreConjugation parameters).norm_map field),
      gradeCoreConjugation_involutive parameters, ?_⟩
    intro field
    simpa only [GradeCoreReality] using
      gradeCoreConjugation_fixed_iff_reality parameters field

end Grad.CartesianState
