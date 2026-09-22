import AJE44OriginalSharedInsertedGrade

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 300000
namespace Grad.AnnularHighGenerators
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongOrbit

private theorem hilbertPair_ext {E F : Type*} (first second : WithLp 2 (E × F))
    (left : first.ofLp.1 = second.ofLp.1) (right : first.ofLp.2 = second.ofLp.2) : first = second :=
  congrArg (WithLp.toLp 2) (Prod.ext left right)

/-- Grade zero inserts the identity in every coordinate of the actual
independently prescribed strong carrier, including the closed source graphs. -/
theorem strongInsertedGrade_zero_eq (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (data weighted : StrongDataCarrier parameters lower positive bounded 0 0)
    (actual : StrongInsertedGrade parameters lower positive bounded 0 data weighted) : weighted = data := by
  have known : weighted.val.ofLp.1.ofLp.1.ofLp.1 = data.val.ofLp.1.ofLp.1.ofLp.1 := by
    apply PiLp.ext
    intro slot
    apply lp.ext
    funext mode
    simpa only [pow_zero, one_smul] using actual.1 slot mode
  have auxiliary : weighted.val.ofLp.1.ofLp.1.ofLp.2 = data.val.ofLp.1.ofLp.1.ofLp.2 := by
    apply PiLp.ext
    intro slot
    apply lp.ext
    funext mode
    simpa only [pow_zero, one_smul] using actual.2.1 slot mode
  have f0 : weighted.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1 = data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1 := by
    apply lp.ext
    funext mode
    simpa only [pow_zero, one_smul] using actual.2.2.1 mode
  have f2 : weighted.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2 = data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2 := by
    apply lp.ext
    funext mode
    simpa only [pow_zero, one_smul] using actual.2.2.2.1 mode
  have outer : weighted.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1 = data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1 := by
    apply Subtype.ext
    apply lp.ext
    funext mode
    simpa only [pow_zero, one_smul] using actual.2.2.2.2.1 mode
  have incoming : weighted.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2 = data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2 := by
    apply lp.ext
    funext mode
    simpa only [pow_zero, one_smul] using actual.2.2.2.2.2.1 mode
  have low : weighted.val.ofLp.2 = data.val.ofLp.2 := by
    apply lp.ext
    funext index
    simpa only [pow_zero, one_smul] using actual.2.2.2.2.2.2 index
  apply Subtype.ext
  exact hilbertPair_ext _ _
    (hilbertPair_ext _ _ (hilbertPair_ext _ _ known auxiliary)
      (hilbertPair_ext _ _ (hilbertPair_ext _ _ f0 f2) (hilbertPair_ext _ _ outer incoming))) low

end Grad.AnnularHighGenerators
