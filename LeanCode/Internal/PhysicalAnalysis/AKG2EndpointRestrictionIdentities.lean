import AKG1FullFiveBlockEndpointRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularRestriction
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.SourceCollarDivision Grad.AnnularSourceGraph Grad.AnnularCurrentSource
open Grad.AnnularForwardTraces Grad.AnnularStrongOrbit Grad.AnnularLowEnergy
open Grad.AnnularForwardDatum Grad.AnnularCrossMaps Grad.AnnularCoupledInverse
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule

theorem originalRetainedRestriction_id (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : OriginalCoupledSpace lower length positive) :
    originalRetainedRestriction parameters lower lower length positive positive bounded lengthPositive le_rfl field = field := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  exact Prod.ext (originalHighRestriction_id lower length positive bounded lengthPositive field.ofLp.1)
    (originalLowEndpointRestriction_id parameters lower length positive bounded lengthPositive field.ofLp.2)

theorem originalRetainedRestriction_comp (parameters : PhaseParameters) (lower middle upper length : ℝ)
    (lowerPositive : 0 < lower) (middlePositive : 0 < middle) (upperPositive : 0 < upper)
    (upperBounded : upper < 1) (lengthPositive : 0 < length) (first : lower ≤ middle) (second : middle ≤ upper)
    (field : OriginalCoupledSpace lower length lowerPositive) :
    originalRetainedRestriction parameters middle upper length middlePositive upperPositive upperBounded lengthPositive second
      (originalRetainedRestriction parameters lower middle length lowerPositive middlePositive (second.trans_lt upperBounded) lengthPositive first field) =
    originalRetainedRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive (first.trans second) field := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  exact Prod.ext
    (originalHighRestriction_comp lower middle upper length lowerPositive middlePositive upperPositive upperBounded lengthPositive first second field.ofLp.1)
    (originalLowEndpointRestriction_comp parameters lower middle upper length first second lowerPositive middlePositive upperPositive upperBounded lengthPositive field.ofLp.2)

theorem originalFiveBlockRestriction_id (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : ForwardFiveBlocks parameters lower length positive) :
    originalFiveBlockRestriction parameters lower lower length positive positive bounded lengthPositive le_rfl field = field := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  exact Prod.ext (originalRetainedRestriction_id parameters lower length positive bounded lengthPositive field.ofLp.1)
    (originalFullSourceRestriction_id parameters lower field.ofLp.2)

theorem originalFiveBlockRestriction_comp (parameters : PhaseParameters) (lower middle upper length : ℝ)
    (lowerPositive : 0 < lower) (middlePositive : 0 < middle) (upperPositive : 0 < upper)
    (upperBounded : upper < 1) (lengthPositive : 0 < length) (first : lower ≤ middle) (second : middle ≤ upper)
    (field : ForwardFiveBlocks parameters lower length lowerPositive) :
    originalFiveBlockRestriction parameters middle upper length middlePositive upperPositive upperBounded lengthPositive second
      (originalFiveBlockRestriction parameters lower middle length lowerPositive middlePositive (second.trans_lt upperBounded) lengthPositive first field) =
    originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive (first.trans second) field := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  exact Prod.ext
    (originalRetainedRestriction_comp parameters lower middle upper length lowerPositive middlePositive upperPositive upperBounded lengthPositive first second field.ofLp.1)
    (originalFullSourceRestriction_comp parameters lower middle upper first second field.ofLp.2)

variable (parameters : PhaseParameters) (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)

/-- Restriction of the SAME physical retained pair in its actual weighted graphs. -/
def coupledEndpointRestriction : CoupledSpace lower length lowerPositive lengthPositive →L[ℂ]
    CoupledSpace upper length upperPositive lengthPositive :=
  restrictionPairMap
    (highWeightedRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included)
    (lowEnergyRestriction lower upper length included lowerPositive upperPositive upperBounded)

theorem coupledEndpointRestriction_bound (field : CoupledSpace lower length lowerPositive lengthPositive) :
    ‖coupledEndpointRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field‖ ≤ ‖field‖ :=
  restrictionPairMap_norm_le _ _
    (highWeightedRestriction_bound lower upper length lowerPositive upperPositive upperBounded lengthPositive included)
    (lowEnergyRestriction_bound lower upper length included lowerPositive upperPositive upperBounded) field

/-- The original endpoint-changing restriction is exactly conjugate to the
genuine graph restriction by the accepted original BF6 equivalences. -/
theorem originalRetainedRestriction_weighted (field : OriginalCoupledSpace lower length lowerPositive) :
    originalCoupledEquivalence parameters upper length upperPositive upperBounded.le lengthPositive
      (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included field) =
    coupledEndpointRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included
      (originalCoupledEquivalence parameters lower length lowerPositive (included.trans upperBounded.le) lengthPositive field) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  exact Prod.ext
    (originalHighRestriction_weighted lower upper length lowerPositive upperPositive upperBounded lengthPositive included field.ofLp.1)
    (originalLowEndpointRestriction_weighted parameters lower upper length included lowerPositive upperPositive upperBounded lengthPositive field.ofLp.2)

end Grad.AnnularRestriction
