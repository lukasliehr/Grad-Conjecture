import AKR34ExactTupleObservationAdditivity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 400000
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
open Grad.AnnularForwardDatum Grad.AnnularForwardTraces Grad.AnnularStrongOrbit
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule

variable {parameters : PhaseParameters} {length compact lower : ℝ} {positive : 0 < lower} {bounded : lower < 1}
    {lengthPositive : 0 < length} {state : RetainedInverseState parameters length compact}
    {tuple : OriginalSmoothTuple parameters lower} {point : OriginalFiveBlockAmbient parameters lower length positive}

theorem originalTupleObservation_real_smul (scalar : ℝ)
    (represented : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple point) :
    OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state
      (scalar • tuple) (scalar • point) := by
  constructor
  · intro radius mode
    change originalTupleCoefficientLinear parameters lower 0 radius mode (scalar • tuple) =
      originalRetainedPressurePointLinear parameters lower length positive bounded lengthPositive radius mode (scalar • point.ofLp.1)
    rw [LinearMap.map_smul_of_tower,LinearMap.map_smul_of_tower]
    exact congrArg (fun value : ComplexEuclidean 1 => scalar • value) (represented.pressure radius mode)
  · intro radius mode
    change originalTupleCoefficientLinear parameters lower 1 radius mode (scalar • tuple) =
      originalRetainedXiPointLinear parameters lower length positive bounded lengthPositive radius mode (scalar • point.ofLp.1)
    rw [LinearMap.map_smul_of_tower,LinearMap.map_smul_of_tower]
    exact congrArg (fun value : ComplexEuclidean 1 => scalar • value) (represented.scalar radius mode)
  · filter_upwards [represented.sourceZero,originalF1Coefficient_real_smul_ae parameters lower positive bounded.le scalar
      (unweightedSourceF0Bulk parameters lower point.ofLp.2.ofLp.1.ofLp.1),ae_restrict_mem measurableSet_Icc] with radius same stored inside
    intro mode
    change originalPhysicalCoefficient ((scalar • tuple).val 2) radius mode =
      originalF1Coefficient parameters lower positive bounded.le
        (unweightedSourceF0Bulk parameters lower (scalar • point.ofLp.2.ofLp.1.ofLp.1)) radius mode
    rw [map_smul,stored mode]
    exact ((originalTupleCoefficientLinear parameters lower 2 ⟨radius,inside⟩ mode).map_smul_of_tower scalar tuple).trans
      (congrArg (fun value : ComplexEuclidean 1 => scalar • value) (same mode))
  · filter_upwards [represented.sourceTwo,originalF1Coefficient_real_smul_ae parameters lower positive bounded.le scalar
      (unweightedSourceF2Bulk parameters lower point.ofLp.2.ofLp.1.ofLp.2),ae_restrict_mem measurableSet_Icc] with radius same stored inside
    intro mode
    change originalPhysicalCoefficient ((scalar • tuple).val 3) radius mode =
      originalF1Coefficient parameters lower positive bounded.le
        (unweightedSourceF2Bulk parameters lower (scalar • point.ofLp.2.ofLp.1.ofLp.2)) radius mode
    rw [map_smul,stored mode]
    exact ((originalTupleCoefficientLinear parameters lower 3 ⟨radius,inside⟩ mode).map_smul_of_tower scalar tuple).trans
      (congrArg (fun value : ComplexEuclidean 1 => scalar • value) (same mode))
  · filter_upwards [represented.firstResidual,originalF1Coefficient_real_smul_ae parameters lower positive bounded.le scalar
      point.ofLp.2.ofLp.2.ofLp.1] with radius same stored
    intro inside mode
    change originalTupleF1 parameters length compact lower positive state (scalar • tuple) ⟨radius,inside⟩ mode =
      originalF1Coefficient parameters lower positive bounded.le (scalar • point.ofLp.2.ofLp.2.ofLp.1) radius mode
    rw [stored mode,← originalTupleF1Linear_apply,LinearMap.map_smul_of_tower,originalTupleF1Linear_apply]
    exact congrArg (fun value : ComplexEuclidean 1 => scalar • value) (same inside mode)
  · filter_upwards [represented.thirdResidual,originalG3Coefficient_real_smul_ae parameters lower positive bounded.le scalar
      point.ofLp.2.ofLp.2.ofLp.2] with radius same stored
    intro inside mode
    change originalTupleG3 parameters length compact lower positive state (scalar • tuple) ⟨radius,inside⟩ mode =
      originalG3Coefficient parameters lower positive bounded.le (scalar • point.ofLp.2.ofLp.2.ofLp.2) radius mode
    rw [stored mode,← originalTupleG3Linear_apply,LinearMap.map_smul_of_tower,originalTupleG3Linear_apply]
    exact congrArg (fun value : ComplexEuclidean 1 => scalar • value) (same inside mode)

end Grad.AnnularOriginalCoreRealization
