import AW3Axes

namespace Grad.AnalyticWeights.Higher

universe valueUniverse

theorem blockGoal : BlockGoal.{valueUniverse} :=
  ⟨coordinateGoal, rankZeroGoal, cellGoal, ratioGoal, diagonalFormula, coefficientGoal,
    allocationGoal, axisGoal, zeroScaleGoal,
    ⟨commonConstant, commonConstant_zero, commonConstant_pos, profileGoal, phaseGoal,
      exponentialGoal, weightGoal, diagonalBoundGoal, coefficientBoundGoal⟩⟩

end Grad.AnalyticWeights.Higher
