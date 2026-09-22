import FC3Interface

noncomputable section

namespace Grad.CartesianState

theorem coordinateBlock : CoordinateBlockGoal := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun _ field => closedContinuous_memLp field
  · exact fun _ parameters coefficients => mem_originalCore_iff parameters coefficients
  · intro dimension parameters grade
    exact ⟨cartesianGradeCoordinates parameters grade,
      cartesianGradeCoordinates_apply parameters grade,
      cartesianGradeCoordinates_norm_sq_expanded parameters grade⟩

end Grad.CartesianState

