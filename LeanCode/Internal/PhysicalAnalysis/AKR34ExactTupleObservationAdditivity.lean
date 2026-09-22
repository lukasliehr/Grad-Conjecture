import AKR33OriginalRetainedPhysicalLinearMaps

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow Grad.AnnularLowEnergy Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger

open Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularHighTilt

open Grad.AnnularFullGraph

open Grad.AnnularHighRadial Grad.AnnularTiltedReference Grad.AnnularOmegaGraph Grad.CircularHighRegularity

open Grad.AnnularCurrentLow
open Grad.AnnularCurrentSource
open Grad.AnnularStrongData
variable {parameters : PhaseParameters} {length compact lower : ℝ} {positive : 0 < lower} {bounded : lower < 1}
    {lengthPositive : 0 < length} {state : RetainedInverseState parameters length compact}
    {firstTuple secondTuple : OriginalSmoothTuple parameters lower}
    {firstPoint secondPoint : OriginalFiveBlockAmbient parameters lower length positive}

theorem originalTupleObservation_add
    (first : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state firstTuple firstPoint)
    (second : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state secondTuple secondPoint) :
    OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state
      (firstTuple+secondTuple) (firstPoint+secondPoint) := by
  constructor
  · intro radius mode
    change originalTupleCoefficientLinear parameters lower 0 radius mode (firstTuple+secondTuple) =
      originalRetainedPressurePointLinear parameters lower length positive bounded lengthPositive radius mode
        (firstPoint.ofLp.1+secondPoint.ofLp.1)
    rw [map_add,map_add]
    exact congrArg₂ (· + ·) (first.pressure radius mode) (second.pressure radius mode)
  · intro radius mode
    change originalTupleCoefficientLinear parameters lower 1 radius mode (firstTuple+secondTuple) =
      originalRetainedXiPointLinear parameters lower length positive bounded lengthPositive radius mode
        (firstPoint.ofLp.1+secondPoint.ofLp.1)
    rw [map_add,map_add]
    exact congrArg₂ (· + ·) (first.scalar radius mode) (second.scalar radius mode)
  · filter_upwards [first.sourceZero,second.sourceZero,originalF1Coefficient_add_ae parameters lower positive bounded.le
      (unweightedSourceF0Bulk parameters lower firstPoint.ofLp.2.ofLp.1.ofLp.1)
      (unweightedSourceF0Bulk parameters lower secondPoint.ofLp.2.ofLp.1.ofLp.1),ae_restrict_mem measurableSet_Icc] with radius a b stored inside
    intro mode
    change originalPhysicalCoefficient ((firstTuple+secondTuple).val 2) radius mode =
      originalF1Coefficient parameters lower positive bounded.le
        (unweightedSourceF0Bulk parameters lower (firstPoint.ofLp.2.ofLp.1.ofLp.1+secondPoint.ofLp.2.ofLp.1.ofLp.1)) radius mode
    rw [map_add,stored mode]
    exact ((originalTupleCoefficientLinear parameters lower 2 ⟨radius,inside⟩ mode).map_add firstTuple secondTuple).trans
      (congrArg₂ (· + ·) (a mode) (b mode))
  · filter_upwards [first.sourceTwo,second.sourceTwo,originalF1Coefficient_add_ae parameters lower positive bounded.le
      (unweightedSourceF2Bulk parameters lower firstPoint.ofLp.2.ofLp.1.ofLp.2)
      (unweightedSourceF2Bulk parameters lower secondPoint.ofLp.2.ofLp.1.ofLp.2),ae_restrict_mem measurableSet_Icc] with radius a b stored inside
    intro mode
    change originalPhysicalCoefficient ((firstTuple+secondTuple).val 3) radius mode =
      originalF1Coefficient parameters lower positive bounded.le
        (unweightedSourceF2Bulk parameters lower (firstPoint.ofLp.2.ofLp.1.ofLp.2+secondPoint.ofLp.2.ofLp.1.ofLp.2)) radius mode
    rw [map_add,stored mode]
    exact ((originalTupleCoefficientLinear parameters lower 3 ⟨radius,inside⟩ mode).map_add firstTuple secondTuple).trans
      (congrArg₂ (· + ·) (a mode) (b mode))
  · filter_upwards [first.firstResidual,second.firstResidual,originalF1Coefficient_add_ae parameters lower positive bounded.le
      firstPoint.ofLp.2.ofLp.2.ofLp.1 secondPoint.ofLp.2.ofLp.2.ofLp.1] with radius a b stored
    intro inside mode
    change originalTupleF1 parameters length compact lower positive state (firstTuple+secondTuple) ⟨radius,inside⟩ mode =
      originalF1Coefficient parameters lower positive bounded.le (firstPoint.ofLp.2.ofLp.2.ofLp.1+secondPoint.ofLp.2.ofLp.2.ofLp.1) radius mode
    rw [stored mode,← originalTupleF1Linear_apply, map_add,originalTupleF1Linear_apply,originalTupleF1Linear_apply]
    exact congrArg₂ (· + ·) (a inside mode) (b inside mode)
  · filter_upwards [first.thirdResidual,second.thirdResidual,originalG3Coefficient_add_ae parameters lower positive bounded.le
      firstPoint.ofLp.2.ofLp.2.ofLp.2 secondPoint.ofLp.2.ofLp.2.ofLp.2] with radius a b stored
    intro inside mode
    change originalTupleG3 parameters length compact lower positive state (firstTuple+secondTuple) ⟨radius,inside⟩ mode =
      originalG3Coefficient parameters lower positive bounded.le (firstPoint.ofLp.2.ofLp.2.ofLp.2+secondPoint.ofLp.2.ofLp.2.ofLp.2) radius mode
    rw [stored mode,← originalTupleG3Linear_apply, map_add,originalTupleG3Linear_apply,originalTupleG3Linear_apply]
    exact congrArg₂ (· + ·) (a inside mode) (b inside mode)

end Grad.AnnularOriginalCoreRealization
