import AW2Weights

namespace Grad.AnalyticWeights.Calculus

theorem blockGoal : BlockGoal :=
  ⟨formulaGoal, smoothGoal, orthogonalGoal, firstGoal, hessianGoal, axisGoal,
    weightDerivativeGoal, weightAxisGoal, firstNormGoal, zeroGoal⟩

end Grad.AnalyticWeights.Calculus
