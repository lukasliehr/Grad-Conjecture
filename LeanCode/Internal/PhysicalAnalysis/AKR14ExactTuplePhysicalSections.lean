import AKR13FaithfulTupleRadialSections
import AKR12GenuineOriginalAJTupleGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.AnnularHighRadial Grad.AnnularHighTilt Grad.AnnularFluxTrace Grad.CircularHighRegularity Grad.AnnularVariational
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)

def tuplePhysicalSection (mode : ℤ × ℤ) : RadialContinuousSection 1 lower :=
  radialSectionScalar lower (annularInversePhase parameters mode.2)
    (tupleConjugatedJetSection parameters lower bounded tuple slot 0 mode)

theorem tuplePhysicalSection_value (mode : ℤ × ℤ) (radius : Icc lower (1 : ℝ)) :
    tuplePhysicalSection parameters lower bounded tuple slot mode radius =
      originalPhysicalCoefficient (tuple.val slot) radius.val mode := by
  change annularInversePhase parameters mode.2 radius.val •
    tupleConjugatedJetSection parameters lower bounded tuple slot 0 mode radius = _
  rw [tupleConjugatedJetSection_value]
  change Real.exp (-radialPhase parameters radius.val mode.2) •
    (Real.exp (radialPhase parameters radius.val mode.2) • originalPhysicalCoefficient (tuple.val slot) radius.val mode) = _
  rw [Real.exp_neg,smul_smul,inv_mul_cancel₀ (Real.exp_pos _).ne',one_smul]

theorem rawHighDecode_weighted_sqrt (field : Grad.AnnularVariational.AnnularBulk lower)
    (mode : Grad.AnnularVariational.HighAnnularMode) (value : CollarL2 (ComplexEuclidean 1) lower)
    (stored : field mode = radialSqrtMap 1 lower value) :
    collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
      (radialOrdinary 1 lower positive (highBulkWeight lower positive bounded.le field mode)) =
      collarScalar 1 lower (annularInversePhase parameters mode.val.2) value := by
  change collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
    (radialOrdinary 1 lower positive (scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
      (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded.le) (field mode))) = _
  rw [stored,scalarRadialMap_eq_collarScalar,radialOrdinary_collarScalar,radialOrdinary_sqrt,collarScalar_mul_apply]
  congr 1
  congr 1
  apply ContinuousMap.ext
  intro radius
  change (highPowerCurve lower highTiltExponent positive radius * annularInversePhase parameters mode.val.2 radius) *
    highPowerCurve lower (-highTiltExponent) positive radius = annularInversePhase parameters mode.val.2 radius
  calc
    _ = (highPowerCurve lower (-highTiltExponent) positive radius * highPowerCurve lower highTiltExponent positive radius) *
      annularInversePhase parameters mode.val.2 radius := by ring
    _ = _ := by rw [highPowerCurve_inverse,one_mul]

end Grad.AnnularOriginalCoreRealization
