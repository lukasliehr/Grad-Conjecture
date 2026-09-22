import WM1Smooth

namespace Grad.Mollifier.WeakJets

theorem dependentGoal : DependentGoal :=
  ⟨averagedWeakGoal, cellNaturalityGoal, ambientGoal, graphGoal, integralGoal,
    liftGoal, contractionGoal, approximationGoal, regularizationGoal, smoothGoal, zeroGoal⟩

theorem blockGoal : BlockGoal := ⟨independentGoal, dependentGoal⟩

end Grad.Mollifier.WeakJets
