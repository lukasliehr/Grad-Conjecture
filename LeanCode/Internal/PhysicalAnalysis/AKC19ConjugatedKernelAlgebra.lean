import AKC17PrimitiveConjugatedKernelRegularity
import AKC18FiniteGradeAlgebraClosure
import AKC11ReservedKernelContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 350000
open Set
open scoped BigOperators ENNReal Topology ContDiff
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.BoundaryLift Grad.AnnularKernelL2
open Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.AnnularRadialSmoothness

def SmoothConjugatedFamily {source target : ℕ} (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target) : Prop :=
  FiniteGradeSmooth parameters (Icc lower 1) (fun grade radius =>
    bulkKernelAction parameters grade (collarRadius lower positive bounded radius)
      (kernel (collarRadius lower positive bounded radius)))

theorem smoothConjugatedFamily_coherent {source target : ℕ} (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target) :
    GradeCoherentOn parameters (Icc lower 1) (fun grade radius =>
      bulkKernelAction parameters grade (collarRadius lower positive bounded radius)
        (kernel (collarRadius lower positive bounded radius))) := by
  intro grade reserve radius _
  exact bulkKernelAction_reserve parameters grade reserve _ _

theorem bulkKernelAction_neg {source target : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (radius : RadialPoint) (kernel : RadialKernel parameters radius source target) :
    bulkKernelAction parameters grade radius (fullKernelNeg kernel) =
      -(bulkKernelAction parameters grade radius kernel) := by
  apply ContinuousLinearMap.ext
  intro field
  apply phaseObservation_injective parameters radius target
  change phaseObservation parameters radius target (bulkKernelAction parameters grade radius (fullKernelNeg kernel) field) =
    phaseObservation parameters radius target (-(bulkKernelAction parameters grade radius kernel field))
  rw [phaseObservation_kernel, polynomialKernelAction_neg, map_neg, phaseObservation_kernel]
  rfl

variable {source middle target : ℕ} {parameters : PhaseParameters} {lower : ℝ}
    {positive : 0 < lower} {bounded : lower ≤ 1}

theorem SmoothConjugatedFamily.add
    {first second : (radius : RadialPoint) → RadialKernel parameters radius source target}
    (one : SmoothConjugatedFamily parameters lower positive bounded first)
    (two : SmoothConjugatedFamily parameters lower positive bounded second) :
    SmoothConjugatedFamily parameters lower positive bounded (fun radius => fullKernelAdd (first radius) (second radius)) :=
  (FiniteGradeSmooth.add one two).congr (fun grade _radius _ => bulkKernelAction_add parameters grade _ _ _)

theorem SmoothConjugatedFamily.neg
    {kernel : (radius : RadialPoint) → RadialKernel parameters radius source target}
    (smooth : SmoothConjugatedFamily parameters lower positive bounded kernel) :
    SmoothConjugatedFamily parameters lower positive bounded (fun radius => fullKernelNeg (kernel radius)) :=
  (FiniteGradeSmooth.neg smooth).congr (fun grade _radius _ => bulkKernelAction_neg parameters grade _ _)

theorem SmoothConjugatedFamily.sub
    {first second : (radius : RadialPoint) → RadialKernel parameters radius source target}
    (one : SmoothConjugatedFamily parameters lower positive bounded first)
    (two : SmoothConjugatedFamily parameters lower positive bounded second) :
    SmoothConjugatedFamily parameters lower positive bounded (fun radius => fullKernelSub (first radius) (second radius)) :=
  one.add two.neg

theorem SmoothConjugatedFamily.comp
    {outer : (radius : RadialPoint) → RadialKernel parameters radius middle target}
    {inner : (radius : RadialPoint) → RadialKernel parameters radius source middle}
    (one : SmoothConjugatedFamily parameters lower positive bounded outer)
    (two : SmoothConjugatedFamily parameters lower positive bounded inner) :
    SmoothConjugatedFamily parameters lower positive bounded (fun radius => fullKernelComposition (outer radius) (inner radius)) :=
  (FiniteGradeSmooth.comp one two (smoothConjugatedFamily_coherent parameters lower positive bounded inner)).congr
    (fun grade _radius _ => bulkKernelAction_composition parameters grade _ _ _)

theorem SmoothConjugatedFamily.smul
    {kernel : (radius : RadialPoint) → RadialKernel parameters radius source target}
    (smooth : SmoothConjugatedFamily parameters lower positive bounded kernel)
    (scalar : ℝ → ℂ) (scalarSmooth : ContDiffOn ℝ ∞ scalar (Icc lower 1)) :
    SmoothConjugatedFamily parameters lower positive bounded (fun radius => fullKernelSmul (scalar radius.val) (kernel radius)) := by
  apply (FiniteGradeSmooth.smul smooth scalarSmooth).congr
  intro grade radius inside
  rw [bulkKernelAction_smul, collarRadius_literal lower positive bounded radius inside]

end Grad.AnnularWeightedSmoothness
