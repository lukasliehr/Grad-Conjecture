import AKR32OriginalPhysicalDecoderLinearity

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
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length)

def originalRetainedXiPointLinear (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    OriginalCoupledSpace lower length positive →ₗ[ℂ] ComplexEuclidean 1 :=
  (LinearMap.proj mode).comp ((LinearMap.proj radius).comp
    ((coupledXiPhysicalLinear parameters lower length positive bounded lengthPositive).comp
      (originalCoupledEquivalence parameters lower length positive bounded.le lengthPositive).toLinearMap))

def originalRetainedPressurePointLinear (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    OriginalCoupledSpace lower length positive →ₗ[ℂ] ComplexEuclidean 1 :=
  angularInverseMultiplier mode • (LinearMap.proj mode).comp ((LinearMap.proj radius).comp
    ((coupledXPhysicalLinear parameters lower length positive bounded lengthPositive).comp
      (originalCoupledEquivalence parameters lower length positive bounded.le lengthPositive).toLinearMap))

end Grad.AnnularOriginalCoreRealization
