import AJW5OriginalHighEndpointRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularReconstruction Grad.AnnularOmegaGraph
open Grad.AnnularCrossMaps Grad.AnnularOriginalHigh

theorem highEnergyRestriction_core (lower upper length : ℝ) (lowerPositive : 0 < lower)
    (upperPositive : 0 < upper) (included : lower ≤ upper)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    highEnergyRestriction lower upper length lowerPositive upperPositive included
      (annularEnergyCoreInto lower length lowerPositive core) = annularEnergyCoreInto upper length upperPositive core :=
  Subtype.ext (highEnergyAmbientRestriction_core lower upper length lowerPositive upperPositive included core)

theorem highEnergyRestriction_id (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : annularEnergySpace lower length positive) :
    highEnergyRestriction lower lower length positive positive le_rfl field = field := by
  apply annularEnergyValue_injective lower length positive bounded
  rw [highEnergyRestriction_value, collarBulkRestriction_id]

theorem highEnergyRestriction_comp (lower middle upper length : ℝ)
    (lowerPositive : 0 < lower) (middlePositive : 0 < middle) (upperPositive : 0 < upper)
    (upperBounded : upper < 1) (first : lower ≤ middle) (second : middle ≤ upper)
    (field : annularEnergySpace lower length lowerPositive) :
    highEnergyRestriction middle upper length middlePositive upperPositive second
      (highEnergyRestriction lower middle length lowerPositive middlePositive first field) =
    highEnergyRestriction lower upper length lowerPositive upperPositive (first.trans second) field := by
  apply annularEnergyValue_injective upper length upperPositive upperBounded
  rw [highEnergyRestriction_value, highEnergyRestriction_value, highEnergyRestriction_value,
    collarBulkRestriction_comp]

theorem highOmegaRestriction_id (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length) (field : annularOmegaGraph lower length positive lengthPositive) :
    highOmegaRestriction lower lower length positive positive bounded lengthPositive le_rfl field = field := by
  apply annularOmegaGraph_value_injective lower length positive bounded lengthPositive
  change collarBulkRestriction HighAnnularMode 1 lower lower le_rfl (field.val 0) = field.val 0
  exact collarBulkRestriction_id HighAnnularMode 1 lower (field.val 0)

theorem highOmegaRestriction_comp (lower middle upper length : ℝ)
    (lowerPositive : 0 < lower) (middlePositive : 0 < middle) (upperPositive : 0 < upper)
    (upperBounded : upper < 1) (lengthPositive : 0 < length) (first : lower ≤ middle) (second : middle ≤ upper)
    (field : annularOmegaGraph lower length lowerPositive lengthPositive) :
    highOmegaRestriction middle upper length middlePositive upperPositive upperBounded lengthPositive second
      (highOmegaRestriction lower middle length lowerPositive middlePositive (second.trans_lt upperBounded) lengthPositive first field) =
    highOmegaRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive (first.trans second) field := by
  apply annularOmegaGraph_value_injective upper length upperPositive upperBounded lengthPositive
  change collarBulkRestriction HighAnnularMode 1 middle upper second
    (collarBulkRestriction HighAnnularMode 1 lower middle first (field.val 0)) =
      collarBulkRestriction HighAnnularMode 1 lower upper (first.trans second) (field.val 0)
  exact collarBulkRestriction_comp HighAnnularMode 1 lower middle upper first second (field.val 0)

theorem highWeightedRestriction_id (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length) (field : CrossHighSpace lower length positive lengthPositive) :
    highWeightedRestriction lower lower length positive positive bounded lengthPositive le_rfl field = field := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext
  · exact highEnergyRestriction_id lower length positive bounded field.ofLp.1
  · exact highOmegaRestriction_id lower length positive bounded lengthPositive field.ofLp.2

theorem highWeightedRestriction_comp (lower middle upper length : ℝ)
    (lowerPositive : 0 < lower) (middlePositive : 0 < middle) (upperPositive : 0 < upper)
    (upperBounded : upper < 1) (lengthPositive : 0 < length) (first : lower ≤ middle) (second : middle ≤ upper)
    (field : CrossHighSpace lower length lowerPositive lengthPositive) :
    highWeightedRestriction middle upper length middlePositive upperPositive upperBounded lengthPositive second
      (highWeightedRestriction lower middle length lowerPositive middlePositive (second.trans_lt upperBounded) lengthPositive first field) =
    highWeightedRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive (first.trans second) field := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext
  · exact highEnergyRestriction_comp lower middle upper length lowerPositive middlePositive upperPositive upperBounded first second field.ofLp.1
  · exact highOmegaRestriction_comp lower middle upper length lowerPositive middlePositive upperPositive upperBounded lengthPositive first second field.ofLp.2

theorem originalHighRestriction_id (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length) (field : OriginalHighSpace lower length positive) :
    originalHighRestriction lower lower length positive positive bounded lengthPositive le_rfl field = field := by
  apply (originalHighTiltEquivalence lower length positive bounded.le lengthPositive).injective
  rw [originalHighRestriction_weighted, highWeightedRestriction_id]

theorem originalHighRestriction_comp (lower middle upper length : ℝ)
    (lowerPositive : 0 < lower) (middlePositive : 0 < middle) (upperPositive : 0 < upper)
    (upperBounded : upper < 1) (lengthPositive : 0 < length) (first : lower ≤ middle) (second : middle ≤ upper)
    (field : OriginalHighSpace lower length lowerPositive) :
    originalHighRestriction middle upper length middlePositive upperPositive upperBounded lengthPositive second
      (originalHighRestriction lower middle length lowerPositive middlePositive (second.trans_lt upperBounded) lengthPositive first field) =
    originalHighRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive (first.trans second) field := by
  apply (originalHighTiltEquivalence upper length upperPositive upperBounded.le lengthPositive).injective
  exact (originalHighRestriction_weighted middle upper length middlePositive upperPositive upperBounded lengthPositive second
      (originalHighRestriction lower middle length lowerPositive middlePositive (second.trans_lt upperBounded) lengthPositive first field)).trans
    ((congrArg (highWeightedRestriction middle upper length middlePositive upperPositive upperBounded lengthPositive second)
      (originalHighRestriction_weighted lower middle length lowerPositive middlePositive (second.trans_lt upperBounded) lengthPositive first field)).trans
      ((highWeightedRestriction_comp lower middle upper length lowerPositive middlePositive upperPositive upperBounded lengthPositive first second
        (originalHighTiltEquivalence lower length lowerPositive (first.trans (second.trans upperBounded.le)) lengthPositive field)).trans
        (originalHighRestriction_weighted lower upper length lowerPositive upperPositive upperBounded lengthPositive (first.trans second) field).symm))

end Grad.AnnularRestriction
