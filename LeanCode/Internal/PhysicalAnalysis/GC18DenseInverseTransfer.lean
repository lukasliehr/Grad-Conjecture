import GC18APLowering

noncomputable section

namespace Grad.GaugeCoefficients.Physical.RadialLedger

theorem denseComplementInverseTransfer {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (lower : E →L[ℂ] F) (dense : DenseRange lower)
    (highP highA highE : E →L[ℂ] E) (lowP lowA lowE : F →L[ℂ] F)
    (project : ∀ x, lower (highP x) = lowP (lower x))
    (action : ∀ x, lower (highA x) = lowA (lower x))
    (inverse : ∀ x, lower (highE x) = lowE (lower x))
    (laws : ∀ x, highP (highE (highP x)) = highE (highP x) ∧
      highE (highA (highP x)) = highP x ∧ highA (highE (highP x)) = highP x) :
    ∀ y, lowP (lowE (lowP y)) = lowE (lowP y) ∧
      lowE (lowA (lowP y)) = lowP y ∧ lowA (lowE (lowP y)) = lowP y := by
  have preserve (y : F) : lowP (lowE (lowP y)) = lowE (lowP y) := by
    apply isClosed_property dense (isClosed_eq (lowP.continuous.comp (lowE.continuous.comp lowP.continuous))
      (lowE.continuous.comp lowP.continuous)) _ y
    intro x
    simp only [Function.comp_apply]
    rw [← project, ← inverse, ← project]
    exact congrArg lower (laws x).1
  have leftInverse (y : F) : lowE (lowA (lowP y)) = lowP y := by
    apply isClosed_property dense (isClosed_eq (lowE.continuous.comp (lowA.continuous.comp lowP.continuous)) lowP.continuous) _ y
    intro x
    simp only [Function.comp_apply]
    rw [← project, ← action, ← inverse]
    exact congrArg lower (laws x).2.1
  have rightInverse (y : F) : lowA (lowE (lowP y)) = lowP y := by
    apply isClosed_property dense (isClosed_eq (lowA.continuous.comp (lowE.continuous.comp lowP.continuous)) lowP.continuous) _ y
    intro x
    simp only [Function.comp_apply]
    rw [← project, ← inverse, ← action]
    exact congrArg lower (laws x).2.2
  exact fun y => ⟨preserve y, leftInverse y, rightInverse y⟩

end Grad.GaugeCoefficients.Physical.RadialLedger
