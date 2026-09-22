import AKR30LiteralTupleCoordinateLinearity

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
variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (state : RetainedInverseState parameters length compact)

def tupleNormalizedTraceLinear (radius : Icc lower (1 : ℝ)) :
    OriginalSmoothTuple parameters lower →ₗ[ℂ]
      NegativeTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 7 where
  toFun tuple := sevenSlotFlatten _ 0 0 (tupleNormalizedInput parameters lower positive tuple radius)
  map_add' first second := by
    apply NegativeTrace.ext_coefficient
    intro mode
    rw [negativeTraceCoefficient_add,tupleNormalizedInput_coefficient,tupleNormalizedInput_coefficient,tupleNormalizedInput_coefficient]
    exact (originalTupleNormalizedLinear parameters lower radius mode).map_add first second
  map_smul' scalar tuple := by
    apply NegativeTrace.ext_coefficient
    intro mode
    rw [negativeTraceCoefficient_smul,tupleNormalizedInput_coefficient,tupleNormalizedInput_coefficient]
    exact (originalTupleNormalizedLinear parameters lower radius mode).map_smul scalar tuple

def originalTupleRowCoefficientLinear (row : Fin 3) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    OriginalSmoothTuple parameters lower →ₗ[ℂ] ComplexEuclidean 1 :=
  (negativeTraceCoefficientCLM (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 mode).toLinearMap.comp
    ((fullNegativeKernelAction _ 0 0 (lowPhysicalRowKernel parameters length compact state row
      (tupleRadius lower positive radius))).toLinearMap.comp
        (tupleNormalizedTraceLinear parameters lower positive radius))

theorem originalTupleRowCoefficientLinear_apply (row : Fin 3) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ)
    (tuple : OriginalSmoothTuple parameters lower) :
    originalTupleRowCoefficientLinear parameters length compact lower positive state row radius mode tuple =
      negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
        (tuplePhysicalRowTrace parameters length compact lower positive state tuple radius row) mode := rfl

def originalTupleF1Linear (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    OriginalSmoothTuple parameters lower →ₗ[ℂ] ComplexEuclidean 1 :=
  originalTupleSlopeLinear parameters lower 1 radius mode -
    angularMeanFreeMultiplier mode • originalTupleRowCoefficientLinear parameters length compact lower positive state 0 radius mode

def originalTupleG3Linear (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    OriginalSmoothTuple parameters lower →ₗ[ℂ] ComplexEuclidean 1 :=
  ((originalTupleSlopeLinear parameters lower 0 radius mode +
    (radius.val : ℂ)⁻¹ • originalTupleCoefficientLinear parameters lower 0 radius mode) +
    (length : ℂ)⁻¹ • (angularInverseMultiplier mode • (frequencyNumerator (some true) mode •
      originalTupleRowCoefficientLinear parameters length compact lower positive state 1 radius mode))) +
    (radius.val : ℂ)⁻¹ • originalTupleRowCoefficientLinear parameters length compact lower positive state 2 radius mode

theorem originalTupleF1Linear_apply (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ)
    (tuple : OriginalSmoothTuple parameters lower) :
    originalTupleF1Linear parameters length compact lower positive state radius mode tuple =
      originalTupleF1 parameters length compact lower positive state tuple radius mode := by
  change derivWithin (fun location => originalPhysicalCoefficient (tuple.val 1) location mode) (Icc lower 1) radius.val -
    angularMeanFreeMultiplier mode • originalTupleRowCoefficientLinear parameters length compact lower positive state 0 radius mode tuple = _
  rw [originalTupleRowCoefficientLinear_apply,tuplePhysicalRowTrace_first]
  rfl

theorem originalTupleG3Linear_apply (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ)
    (tuple : OriginalSmoothTuple parameters lower) :
    originalTupleG3Linear parameters length compact lower positive state radius mode tuple =
      originalTupleG3 parameters length compact lower positive state tuple radius mode := by
  rw [originalTupleG3_physicalRows]
  rfl

end Grad.AnnularOriginalCoreRealization
