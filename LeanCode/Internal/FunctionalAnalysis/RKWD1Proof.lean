import RKWD1Allocation
import RKWD1CoreIBP
import RKWD1Closure
import RKWD1Density
import RKWD1RankZero

noncomputable section

namespace Grad.RepresentedKernel.WeakDerivatives

universe parameterUniverse

theorem block : BlockGoal.{parameterUniverse} :=
  ⟨chainProducts, allocationIndices, allocationData, allocationCLM, coreIBP, closedWeak,
    densityPassage, rankZero⟩

end Grad.RepresentedKernel.WeakDerivatives
