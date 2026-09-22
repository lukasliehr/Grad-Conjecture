import AKI37LiteralResidualMeanConstraints
import AKE2ForwardDatumBoundsAndCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularSourceGraph
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularFullGraph Grad.AnnularReconstruction
open Grad.AnnularStrongOrbit Grad.AnnularCurrentSource Grad.AnnularForwardDatum Grad.AnnularForwardTraces
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Masking an original F2 graph commutes with its value coordinate; the
radial derivative remains the derivative belonging to that same graph. -/
theorem unweightedSourceF2Bulk_mask (parameters : PhaseParameters) (lower : ℝ)
    (source : HighF2SourceGraph parameters lower) :
    unweightedSourceF2Bulk parameters lower (sourceMeanFreeLp source) =
      sourceMeanFreeLp (unweightedSourceF2Bulk parameters lower source) := by
  apply lp.ext
  funext mode
  change weightedRadialCoordinate 1 lower 0 (sourceMeanFreeLp source mode) = _
  rw [sourceMeanFreeLp_apply,sourceMeanFreeLp_apply]
  by_cases mean : mode.1 = 0
  · rw [if_pos mean,if_pos mean,map_zero]
  · rw [if_neg mean,if_neg mean]
    rfl

attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (tuple : OriginalSmoothTuple parameters lower)
    (point : OriginalFiveBlockAmbient parameters lower length positive)
    (represented : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple point)

include represented

/-- Every represented literal tuple already satisfies the original three
source mean constraints, including the full F2 graph. -/
theorem OriginalTupleObservation.sourceMasks_fixed :
    sourceMeanFreeLp point.ofLp.2.ofLp.1.ofLp.2 = point.ofLp.2.ofLp.1.ofLp.2 ∧
      sourceMeanFreeLp point.ofLp.2.ofLp.2.ofLp.1 = point.ofLp.2.ofLp.2.ofLp.1 ∧
      sourceMeanFreeLp point.ofLp.2.ofLp.2.ofLp.2 = point.ofLp.2.ofLp.2.ofLp.2 := by
  have f2 : sourceMeanFreeLp (unweightedSourceF2Bulk parameters lower point.ofLp.2.ofLp.1.ofLp.2) =
      unweightedSourceF2Bulk parameters lower point.ofLp.2.ofLp.1.ofLp.2 := by
    apply sourceMeanFree_of_physicalZero parameters lower positive bounded.le
    filter_upwards [represented.sourceTwo,ae_restrict_mem measurableSet_Icc] with radius actual inside
    intro cell
    exact (actual (0,cell)).symm.trans (tuple.property.2 3 (by decide) radius inside cell)
  refine ⟨unweightedSourceF2Bulk_faithful parameters lower positive bounded.le
    ((unweightedSourceF2Bulk_mask parameters lower point.ofLp.2.ofLp.1.ofLp.2).trans f2),?_,?_⟩
  · apply sourceMeanFree_of_physicalZero parameters lower positive bounded.le
    filter_upwards [represented.firstResidual,ae_restrict_mem measurableSet_Icc] with radius actual inside
    intro cell
    exact (actual inside (0,cell)).symm.trans
      (originalTuple_residual_meanFree parameters length compact lower positive bounded state tuple ⟨radius,inside⟩ cell).1
  · apply sourceMeanFree_of_physicalZero parameters lower positive bounded.le
    filter_upwards [represented.strengthenedThird,ae_restrict_mem measurableSet_Icc] with radius actual inside
    intro cell
    rw [← actual inside (0,cell),
      (originalTuple_residual_meanFree parameters length compact lower positive bounded state tuple ⟨radius,inside⟩ cell).2,smul_zero]

/-- Canonical forward recovery preserves the literal tuple's entire exact
five-block point, before imposing any equation or inverse condition. -/
theorem OriginalTupleObservation.forwardObservation (lowerHalf : lower ≤ 1/2) :
    originalFiveBlockObservation parameters lower length positive
      (originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state point,point.ofLp.1) = point := by
  have masks := represented.sourceMasks_fixed parameters length compact lower positive bounded lengthPositive state tuple point
  have f2 : sourceMeanFreeLp point.ofLp.2.ofLp.1.ofLp.2 = point.ofLp.2.ofLp.1.ofLp.2 := masks.1
  have f : sourceMeanFreeLp point.ofLp.2.ofLp.2.ofLp.1 = point.ofLp.2.ofLp.2.ofLp.1 := masks.2.1
  have g : sourceMeanFreeLp point.ofLp.2.ofLp.2.ofLp.2 = point.ofLp.2.ofLp.2.ofLp.2 := masks.2.2
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · rfl
  · apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · apply (WithLp.equiv 2 _).injective
      exact Prod.ext (originalForwardDatum_F0 parameters length compact lower positive lowerHalf lengthPositive state point)
        ((originalForwardDatum_F2 parameters length compact lower positive lowerHalf lengthPositive state point).trans f2)
    · apply (WithLp.equiv 2 _).injective
      exact Prod.ext ((originalForwardDatum_F1 parameters length compact lower positive lowerHalf lengthPositive state point).trans f)
        ((originalForwardDatum_G3 parameters length compact lower positive lowerHalf lengthPositive state point).trans g)

end Grad.AnnularOriginalSmoothCore
