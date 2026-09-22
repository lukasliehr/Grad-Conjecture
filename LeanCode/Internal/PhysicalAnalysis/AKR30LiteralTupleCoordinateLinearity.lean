import AKR29ActualCoupledCoefficientLinearMaps

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

variable (parameters : PhaseParameters) (lower : ℝ) (bounded : lower < 1)

def originalTupleCoefficientLinear (slot : Fin 4) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    OriginalSmoothTuple parameters lower →ₗ[ℂ] ComplexEuclidean 1 where
  toFun tuple := originalPhysicalCoefficient (tuple.val slot) radius.val mode
  map_add' first second := originalPhysicalCoefficient_add (first.property.1 slot).1 (second.property.1 slot).1 radius.val radius.property mode
  map_smul' scalar tuple := originalPhysicalCoefficient_smul scalar (tuple.val slot) radius.val mode

def originalTupleSlopeLinear (slot : Fin 4) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    OriginalSmoothTuple parameters lower →ₗ[ℂ] ComplexEuclidean 1 where
  toFun tuple := derivWithin (fun location => originalPhysicalCoefficient (tuple.val slot) location mode) (Icc lower 1) radius.val
  map_add' first second := by
    have equality : EqOn (fun location => originalPhysicalCoefficient ((first+second).val slot) location mode)
        (fun location => originalPhysicalCoefficient (first.val slot) location mode +
          originalPhysicalCoefficient (second.val slot) location mode) (Icc lower 1) := by
      intro location inside
      exact (originalTupleCoefficientLinear parameters lower slot ⟨location,inside⟩ mode).map_add first second
    rw [derivWithin_congr equality (equality radius.property)]
    exact derivWithin_add
      ((originalTuple_coefficient_smooth parameters lower first slot mode).differentiableOn (by simp) radius.val radius.property)
      ((originalTuple_coefficient_smooth parameters lower second slot mode).differentiableOn (by simp) radius.val radius.property)
  map_smul' scalar tuple := by
    have equality : EqOn (fun location => originalPhysicalCoefficient ((scalar • tuple).val slot) location mode)
        (fun location => scalar • originalPhysicalCoefficient (tuple.val slot) location mode) (Icc lower 1) := by
      intro location inside
      exact (originalTupleCoefficientLinear parameters lower slot ⟨location,inside⟩ mode).map_smul scalar tuple
    rw [derivWithin_congr equality (equality radius.property)]
    exact derivWithin_const_smul scalar
      ((originalTuple_coefficient_smooth parameters lower tuple slot mode).differentiableOn (by simp) radius.val radius.property)

def originalTupleNormalizedLinear (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    OriginalSmoothTuple parameters lower →ₗ[ℂ] ComplexEuclidean 7 where
  toFun tuple := originalTupleNormalizedCoefficient parameters lower tuple radius mode
  map_add' first second := by
    have law (slot : Fin 4) : originalPhysicalCoefficient (first.val slot + second.val slot) radius.val mode =
        originalPhysicalCoefficient (first.val slot) radius.val mode + originalPhysicalCoefficient (second.val slot) radius.val mode :=
      originalPhysicalCoefficient_add (first.property.1 slot).1 (second.property.1 slot).1 radius.val radius.property mode
    ext slot
    fin_cases slot <;> simp [originalTupleNormalizedCoefficient,law]
  map_smul' scalar tuple := by
    ext slot
    fin_cases slot <;> simp [originalTupleNormalizedCoefficient,originalPhysicalCoefficient_smul,smul_smul] <;> ring

end Grad.AnnularOriginalCoreRealization
