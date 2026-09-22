import AKR28GenuinePhysicalSectionLinearity

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

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length)

def coupledXiPhysicalLinear : CoupledSpace lower length positive lengthPositive →ₗ[ℂ]
    (Icc lower (1 : ℝ) → (ℤ × ℤ) → ComplexEuclidean 1) where
  toFun field radius mode := sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0 radius mode
  map_add' first second := by
    funext radius mode
    change sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive (first+second) 0 radius mode =
      sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive first 0 radius mode +
        sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive second 0 radius mode
    by_cases high : 3 ≤ |mode.1|
    · rw [sameCoupledXiCoefficient_high parameters lower length positive bounded lengthPositive (first+second) ⟨mode,high⟩,
        sameCoupledXiCoefficient_high parameters lower length positive bounded lengthPositive first ⟨mode,high⟩,
        sameCoupledXiCoefficient_high parameters lower length positive bounded lengthPositive second ⟨mode,high⟩]
      exact congrArg (fun sectionValue : RadialContinuousSection 1 lower => sectionValue radius)
        (rawHighXiSection_add parameters lower length positive bounded first.ofLp.1.ofLp.1 second.ofLp.1.ofLp.1 ⟨mode,high⟩)
    by_cases low : |mode.1| = 1 ∨ |mode.1| = 2
    · simp only [sameCoupledXiCoefficient,dif_neg high,dif_pos low,pow_zero,Complex.ofReal_one,one_smul]
      exact congrArg (fun sectionValue : RadialContinuousSection 1 lower => sectionValue radius)
        (lowPhysicalSection_add parameters lower length positive bounded first.ofLp.2 second.ofLp.2 (0,⟨mode,low⟩))
    · simp only [sameCoupledXiCoefficient,dif_neg high,dif_neg low,add_zero]
  map_smul' scalar field := by
    funext radius mode
    change sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive (scalar • field) 0 radius mode =
      scalar • sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0 radius mode
    by_cases high : 3 ≤ |mode.1|
    · rw [sameCoupledXiCoefficient_high parameters lower length positive bounded lengthPositive (scalar • field) ⟨mode,high⟩,
        sameCoupledXiCoefficient_high parameters lower length positive bounded lengthPositive field ⟨mode,high⟩]
      exact congrArg (fun sectionValue : RadialContinuousSection 1 lower => sectionValue radius)
        (rawHighXiSection_smul parameters lower length positive bounded scalar field.ofLp.1.ofLp.1 ⟨mode,high⟩)
    by_cases low : |mode.1| = 1 ∨ |mode.1| = 2
    · simp only [sameCoupledXiCoefficient,dif_neg high,dif_pos low,pow_zero,Complex.ofReal_one,one_smul]
      exact congrArg (fun sectionValue : RadialContinuousSection 1 lower => sectionValue radius)
        (lowPhysicalSection_smul parameters lower length positive bounded scalar field.ofLp.2 (0,⟨mode,low⟩))
    · simp only [sameCoupledXiCoefficient,dif_neg high,dif_neg low,smul_zero]

def coupledXPhysicalLinear : CoupledSpace lower length positive lengthPositive →ₗ[ℂ]
    (Icc lower (1 : ℝ) → (ℤ × ℤ) → ComplexEuclidean 1) where
  toFun field radius mode := sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0 radius mode
  map_add' first second := by
    funext radius mode
    change sameCoupledXCoefficient parameters lower length positive bounded lengthPositive (first+second) 0 radius mode =
      sameCoupledXCoefficient parameters lower length positive bounded lengthPositive first 0 radius mode +
        sameCoupledXCoefficient parameters lower length positive bounded lengthPositive second 0 radius mode
    by_cases high : 3 ≤ |mode.1|
    · rw [sameCoupledXCoefficient_high parameters lower length positive bounded lengthPositive (first+second) ⟨mode,high⟩,
        sameCoupledXCoefficient_high parameters lower length positive bounded lengthPositive first ⟨mode,high⟩,
        sameCoupledXCoefficient_high parameters lower length positive bounded lengthPositive second ⟨mode,high⟩]
      exact congrArg (fun sectionValue : RadialContinuousSection 1 lower => sectionValue radius)
        (rawHighXSection_add parameters lower length positive bounded lengthPositive first.ofLp.1.ofLp.2 second.ofLp.1.ofLp.2 ⟨mode,high⟩)
    by_cases low : |mode.1| = 1 ∨ |mode.1| = 2
    · simp only [sameCoupledXCoefficient,dif_neg high,dif_pos low,pow_zero,Complex.ofReal_one,one_smul]
      exact congrArg (fun sectionValue : RadialContinuousSection 1 lower => sectionValue radius)
        (lowPhysicalSection_add parameters lower length positive bounded first.ofLp.2 second.ofLp.2 (1,⟨mode,low⟩))
    · simp only [sameCoupledXCoefficient,dif_neg high,dif_neg low,add_zero]
  map_smul' scalar field := by
    funext radius mode
    change sameCoupledXCoefficient parameters lower length positive bounded lengthPositive (scalar • field) 0 radius mode =
      scalar • sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0 radius mode
    by_cases high : 3 ≤ |mode.1|
    · rw [sameCoupledXCoefficient_high parameters lower length positive bounded lengthPositive (scalar • field) ⟨mode,high⟩,
        sameCoupledXCoefficient_high parameters lower length positive bounded lengthPositive field ⟨mode,high⟩]
      exact congrArg (fun sectionValue : RadialContinuousSection 1 lower => sectionValue radius)
        (rawHighXSection_smul parameters lower length positive bounded lengthPositive scalar field.ofLp.1.ofLp.2 ⟨mode,high⟩)
    by_cases low : |mode.1| = 1 ∨ |mode.1| = 2
    · simp only [sameCoupledXCoefficient,dif_neg high,dif_pos low,pow_zero,Complex.ofReal_one,one_smul]
      exact congrArg (fun sectionValue : RadialContinuousSection 1 lower => sectionValue radius)
        (lowPhysicalSection_smul parameters lower length positive bounded scalar field.ofLp.2 (1,⟨mode,low⟩))
    · simp only [sameCoupledXCoefficient,dif_neg high,dif_neg low,smul_zero]

end Grad.AnnularOriginalCoreRealization
