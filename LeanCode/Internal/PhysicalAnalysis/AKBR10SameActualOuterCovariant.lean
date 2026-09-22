import AKBR5SameLiteralOuterSevenTrace
import AKBR9SameOriginalBoundaryProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalKernelOuterUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives
open Grad.AnnularOriginalSmoothCore

/-- Identical full kernel entries with the SAME phase give identical
completed negative actions. This is used only at the original r=1 endpoint. -/
theorem originalSameKernel_action {first second : PhaseParameters} (phase : first=second)
    {input output : ℕ} (left : FullTwoFrequencyKernel first input output) (right : FullTwoFrequencyKernel second input output)
    (same : SameKernelEntries left right) (field : NegativeTrace first 0 0 input) :
    fullNegativeKernelAction first 0 0 left field=fullNegativeKernelAction second 0 0 right field := by
  subst second
  apply NegativeTrace.ext_coefficient first 0 0
  intro mode
  apply (fullNegativeKernelAction_coefficient_hasSum first 0 0 left field mode).unique
  apply (fullNegativeKernelAction_coefficient_hasSum first 0 0 right field mode).congr_fun
  intro shift
  rw [same]

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (state : RetainedInverseState parameters length compact) (tuple : OriginalSmoothTuple parameters lower)

theorem originalTupleNormalized_outer :
    tupleNormalizedInput parameters lower positive tuple ⟨1,bounded.le,le_rfl⟩=
      tupleSevenInput parameters lower positive tuple ⟨1,bounded.le,le_rfl⟩ := by
  apply PiLp.ext
  intro slot
  fin_cases slot
  · rfl
  · change (1:ℂ)⁻¹ • _=_
    simp
  · rfl
  · change (1:ℂ)⁻¹ • _=_
    simp
  · rfl
  · rfl
  · rfl

/-- The original graph's literal outer covariant uses exactly the fixed
BCT covariant kernel; its seven normalization is the identity at r=1. -/
theorem originalTupleCovariant_outer :
    tupleCovariantTrace parameters length compact lower positive state tuple ⟨1,bounded.le,le_rfl⟩=
      fullNegativeKernelAction parameters 0 0 state.boundaryState.covariant
        (sevenSlotFlatten parameters 0 0 (tupleNormalizedInput parameters lower positive tuple ⟨1,bounded.le,le_rfl⟩)) := by
  rw [originalTupleNormalized_outer parameters lower positive bounded tuple]
  exact originalSameKernel_action (radialKernelParameters_one parameters) _ _
    (radialCovariantKernel_one parameters length compact state.val.val state.val.property) _

end Grad.OriginalKernelOuterUniqueness
