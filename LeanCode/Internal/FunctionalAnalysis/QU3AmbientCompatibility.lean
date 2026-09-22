import QU2AmbientInclusions

noncomputable section

namespace Grad.ConstrainedGrades

open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.SmoothingFamily Grad.Constraints
open Grad.RealFixedRanges Grad.CompletedReality Grad.QuotientProjection

theorem xLowering_projection {lower upper : ℕ} (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper) (field : XAmbient parameters upper) :
    xLowering parameters ordered (stateProjection parameters parameter inside upper (large.trans ordered) field) =
      stateProjection parameters parameter inside lower large (xLowering parameters ordered field) := by
  refine isClosed_property (stateToGrade_denseRange parameters upper)
    (isClosed_eq ((xLowering parameters ordered).continuous.comp
      (stateProjection parameters parameter inside upper (large.trans ordered)).continuous)
      ((stateProjection parameters parameter inside lower large).continuous.comp
        (xLowering parameters ordered).continuous)) ?_ field
  intro core
  dsimp only [Function.comp_apply]
  rw [stateProjection_core, xLowering_core, xLowering_core, stateProjection_core]

theorem zLowering_projection {lower upper : ℕ} (parameters : PhaseParameters)
    (large : 3 ≤ lower) (ordered : lower ≤ upper) (field : ZAmbient parameters upper) :
    zLowering parameters ordered (sourceProjection parameters upper (large.trans ordered) field) =
      sourceProjection parameters lower large (zLowering parameters ordered field) := by
  refine isClosed_property (quotientEta_denseRange parameters upper)
    (isClosed_eq ((zLowering parameters ordered).continuous.comp
      (sourceProjection parameters upper (large.trans ordered)).continuous)
      ((sourceProjection parameters lower large).continuous.comp
        (zLowering parameters ordered).continuous)) ?_ field
  intro core
  dsimp only [Function.comp_apply]
  rw [sourceProjection_core, zLowering_core, zLowering_core, sourceProjection_core]

theorem xLowering_conjugation {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (field : XAmbient parameters upper) :
    xLowering parameters ordered (xConjugation parameters upper field) =
      xConjugation parameters lower (xLowering parameters ordered field) := by
  refine isClosed_property (stateToGrade_denseRange parameters upper)
    (isClosed_eq ((xLowering parameters ordered).continuous.comp (xConjugation parameters upper).continuous)
      ((xConjugation parameters lower).continuous.comp (xLowering parameters ordered).continuous)) ?_ field
  intro core
  dsimp only [Function.comp_apply]
  rw [xConjugation_eta, xLowering_core, xLowering_core, xConjugation_eta]

theorem zLowering_conjugation {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (field : ZAmbient parameters upper) :
    zLowering parameters ordered (zConjugation parameters upper field) =
      zConjugation parameters lower (zLowering parameters ordered field) := by
  refine isClosed_property (quotientEta_denseRange parameters upper)
    (isClosed_eq ((zLowering parameters ordered).continuous.comp (zConjugation parameters upper).continuous)
      ((zConjugation parameters lower).continuous.comp (zLowering parameters ordered).continuous)) ?_ field
  intro core
  dsimp only [Function.comp_apply]
  rw [zConjugation_quotientEta, zLowering_core, zLowering_core, zConjugation_quotientEta]

theorem xLowering_self (parameters : PhaseParameters) (grade : ℕ) (field : XAmbient parameters grade) :
    xLowering parameters (le_refl grade) field = field := by
  refine isClosed_property (stateToGrade_denseRange parameters grade)
    (isClosed_eq (xLowering parameters (le_refl grade)).continuous continuous_id) ?_ field
  exact xLowering_core parameters (le_refl grade)

theorem zLowering_self (parameters : PhaseParameters) (grade : ℕ) (field : ZAmbient parameters grade) :
    zLowering parameters (le_refl grade) field = field := by
  refine isClosed_property (quotientEta_denseRange parameters grade)
    (isClosed_eq (zLowering parameters (le_refl grade)).continuous continuous_id) ?_ field
  exact zLowering_core parameters (le_refl grade)

theorem xLowering_trans {lower middle upper : ℕ} (parameters : PhaseParameters)
    (first : lower ≤ middle) (second : middle ≤ upper) (field : XAmbient parameters upper) :
    xLowering parameters first (xLowering parameters second field) =
      xLowering parameters (first.trans second) field := by
  refine isClosed_property (stateToGrade_denseRange parameters upper)
    (isClosed_eq ((xLowering parameters first).continuous.comp (xLowering parameters second).continuous)
      (xLowering parameters (first.trans second)).continuous) ?_ field
  intro core
  dsimp only [Function.comp_apply]
  rw [xLowering_core, xLowering_core, xLowering_core]

theorem zLowering_trans {lower middle upper : ℕ} (parameters : PhaseParameters)
    (first : lower ≤ middle) (second : middle ≤ upper) (field : ZAmbient parameters upper) :
    zLowering parameters first (zLowering parameters second field) =
      zLowering parameters (first.trans second) field := by
  refine isClosed_property (quotientEta_denseRange parameters upper)
    (isClosed_eq ((zLowering parameters first).continuous.comp (zLowering parameters second).continuous)
      (zLowering parameters (first.trans second)).continuous) ?_ field
  intro core
  dsimp only [Function.comp_apply]
  rw [zLowering_core, zLowering_core, zLowering_core]

end Grad.ConstrainedGrades
