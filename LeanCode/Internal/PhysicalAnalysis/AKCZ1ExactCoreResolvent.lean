import AKCV15OriginalBranchInverseTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Grad.NashMoser.InverseCalculus

variable {State Source : Type*} [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Source] [Module ℝ Source]

/-- The resolvent identity is on the actual smooth cores. It uses both
original inverse identities, with no same-grade Banach inverse claim. -/
theorem core_resolvent_identity
    (baseForward pointForward : State →ₗ[ℝ] Source)
    (baseInverse pointInverse : Source →ₗ[ℝ] State)
    (baseRight : ∀ source, baseForward (baseInverse source)=source)
    (pointLeft : ∀ state, pointInverse (pointForward state)=state)
    (source : Source) :
    pointInverse source-baseInverse source =
      -pointInverse ((pointForward-baseForward) (baseInverse source)) := by
  rw [LinearMap.sub_apply,map_sub,pointLeft,baseRight]
  abel

/-- Subtracting the actual derivative candidate leaves only two products:
a first inverse difference times the first forward variation, and the
second-order forward remainder. This is the finite-loss derivative input. -/
theorem core_resolvent_derivative_remainder
    (baseForward pointForward firstVariation : State →ₗ[ℝ] Source)
    (baseInverse pointInverse : Source →ₗ[ℝ] State)
    (baseRight : ∀ source, baseForward (baseInverse source)=source)
    (pointLeft : ∀ state, pointInverse (pointForward state)=state)
    (source : Source) :
    pointInverse source-baseInverse source-(-baseInverse (firstVariation (baseInverse source))) =
      -(pointInverse-baseInverse) (firstVariation (baseInverse source)) -
        pointInverse ((pointForward-baseForward-firstVariation) (baseInverse source)) := by
  rw [core_resolvent_identity baseForward pointForward baseInverse pointInverse baseRight pointLeft]
  simp only [LinearMap.sub_apply,map_sub]
  abel

end Grad.NashMoser.InverseCalculus
