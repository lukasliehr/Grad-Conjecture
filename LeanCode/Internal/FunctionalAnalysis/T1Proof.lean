import T1Approximation
import T1Canonical

namespace Grad.SpatialTranslation

universe valueUniverse otherUniverse

theorem block : BlockGoal.{valueUniverse, otherUniverse} :=
  ⟨isometry, continuity, naturality, canonical, averaging, functional, compactTest,
    contraction, error, smallSupport, cell⟩

end Grad.SpatialTranslation
