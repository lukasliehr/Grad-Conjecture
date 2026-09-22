import AJW8OriginalHighRestrictionGrades

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped Topology
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularSourceGraph

/-- The actual completed outer Sobolev trace is preserved by restriction.
This follows from the same global smooth cores and their genuine endpoint values. -/
theorem highEnergyRestriction_outerTrace (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (field : annularEnergySpace lower length lowerPositive) :
    annularEnergyTrace upper length upperPositive upperBounded lengthPositive 1
      (highEnergyRestriction lower upper length lowerPositive upperPositive included field) =
    annularEnergyTrace lower length lowerPositive (included.trans_lt upperBounded) lengthPositive 1 field := by
  apply isClosed_property (annularEnergyCoreInto_denseRange lower length lowerPositive)
    (isClosed_eq
      ((annularEnergyTrace upper length upperPositive upperBounded lengthPositive 1).continuous.comp
        (highEnergyRestriction lower upper length lowerPositive upperPositive included).continuous)
      (annularEnergyTrace lower length lowerPositive (included.trans_lt upperBounded) lengthPositive 1).continuous) _ field
  intro core
  simp only [Function.comp_apply]
  rw [highEnergyRestriction_core, annularEnergyTrace_core, annularEnergyTrace_core]
  apply lp.ext
  funext mode
  rw [finiteAnnularTraceCore_apply, finiteAnnularTraceCore_apply]
  rfl

end Grad.AnnularRestriction
