import AKM14SameAllGradeWeakLimits

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
namespace Grad.AnnularWeakExhaustion
open Grad.CartesianState Grad.AnnularCoupledInverse Grad.AnnularStrongSolution
open Grad.AnnularHighGenerators Grad.AnnularRestriction

/-- All stored coordinates determine a literal inserted witness uniquely. -/
theorem coupledInsertedGrade_unique (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (grade : ℕ) (field first second : CoupledSpace lower length positive lengthPositive)
    (one : CoupledInsertedGrade lower length positive lengthPositive grade field first)
    (two : CoupledInsertedGrade lower length positive lengthPositive grade field second) : first = second := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext
  · apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
    apply Prod.ext
    · apply Subtype.ext
      apply lp.ext
      funext index
      exact (one.1 index).trans (two.1 index).symm
    · apply Subtype.ext
      apply PiLp.ext
      intro coordinate
      apply lp.ext
      funext index
      exact (one.2.1 coordinate index).trans (two.2.1 coordinate index).symm
  · apply Subtype.ext
    apply PiLp.ext
    intro coordinate
    apply lp.ext
    funext index
    exact (one.2.2 coordinate index).trans (two.2.2 coordinate index).symm

/-- Every extracted grade represents the SAME restricted field. The
compatibility follows from actual stored-coordinate identities, without
pretending that Fourier insertion preserves the variable-coefficient PDE. -/
theorem originalInsertedLimits_restriction_compatible
    (parameters : PhaseParameters) (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper) (grade : ℕ)
    (field : OriginalCoupledSpace lower length lowerPositive)
    (next : OriginalCoupledSpace upper length upperPositive)
    (same : originalRetainedRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included field = next)
    (weighted : CoupledSpace lower length lowerPositive lengthPositive)
    (nextWeighted : CoupledSpace upper length upperPositive lengthPositive)
    (one : CoupledInsertedGrade lower length lowerPositive lengthPositive grade
      (originalCoupledEquivalence parameters lower length lowerPositive (included.trans upperBounded.le) lengthPositive field) weighted)
    (two : CoupledInsertedGrade upper length upperPositive lengthPositive grade
      (originalCoupledEquivalence parameters upper length upperPositive upperBounded.le lengthPositive next) nextWeighted) :
    coupledEndpointRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included weighted = nextWeighted := by
  have fieldIdentity := (originalRetainedRestriction_weighted parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included field).symm.trans
    (congrArg (originalCoupledEquivalence parameters upper length upperPositive upperBounded.le lengthPositive) same)
  have restricted := coupledEndpointRestriction_inserted lower upper length lowerPositive upperPositive upperBounded lengthPositive included grade _ _ one
  have actual := (congrArg (fun base => CoupledInsertedGrade upper length upperPositive lengthPositive grade base
    (coupledEndpointRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included weighted)) fieldIdentity).mp restricted
  exact coupledInsertedGrade_unique upper length upperPositive lengthPositive grade _ _ _ actual two

end Grad.AnnularWeakExhaustion
