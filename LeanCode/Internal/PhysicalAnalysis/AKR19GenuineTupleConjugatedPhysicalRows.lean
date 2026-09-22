import AKR18ExactTupleConjugatedSevenCurve

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
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.AnnularCurrentLow

theorem coherentConjugatedKernelCurve_smooth {source target : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target)
    (curve : ℕ → ℝ → CellL2 source)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1))
    (shift : ∀ grade reserve radius, radius ∈ Icc lower 1 → ∀ mode : ℤ × ℤ,
      curve (grade+reserve) radius mode = (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^reserve •
        curve grade radius mode)
    (grade : ℕ)
    (regularity : ∀ order : ℕ, ∃ reserve : ℕ,
      ContDiffOn ℝ order (radialConjugatedAction parameters lower positive bounded kernel grade reserve) (Icc lower 1)) :
    ContDiffOn ℝ ∞ (fun radius => radialConjugatedAction parameters lower positive bounded kernel grade 0 radius
      (curve grade radius)) (Icc lower 1) := by
  apply contDiffOn_infty.mpr
  intro order
  obtain ⟨reserve, regular⟩ := regularity order
  have realSmooth := ((ContinuousLinearMap.restrictScalarsIsometry ℂ (CellL2 source) (CellL2 target) ℝ ℝ).toContinuousLinearMap.contDiff).comp_contDiffOn regular
  have mapped := realSmooth.clm_apply ((contDiffOn_infty.mp (smooth (grade+reserve))) order)
  apply mapped.congr
  intro radius inside
  exact ((conjugatedKernelAction_same parameters grade reserve (collarRadius lower positive bounded radius)
    (kernel (collarRadius lower positive bounded radius)) _ _ (shift grade reserve radius inside)).trans
    (conjugatedKernelAction_same parameters grade 0 (collarRadius lower positive bounded radius)
      (kernel (collarRadius lower positive bounded radius)) _ _ (fun _ => by rw [pow_zero,one_smul])).symm).symm

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (tuple : OriginalSmoothTuple parameters lower)

theorem tupleConjugatedSevenCurve_shift (grade reserve : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1)
    (mode : ℤ × ℤ) :
    tupleConjugatedSevenCurve parameters lower tuple (grade+reserve) radius mode =
      (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^reserve •
        tupleConjugatedSevenCurve parameters lower tuple grade radius mode := by
  rw [tupleConjugatedSevenCurve_coefficient parameters lower tuple (grade+reserve) ⟨radius,inside⟩ mode,
    tupleConjugatedSevenCurve_coefficient parameters lower tuple grade ⟨radius,inside⟩ mode,
    pow_add,Complex.ofReal_mul,smul_smul]
  simp only [Complex.ofReal_pow,smul_smul]
  change (((Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^grade *
    (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^reserve) *
    (Real.exp (radialPhase parameters radius mode.2) : ℂ)) •
      originalTupleNormalizedCoefficient parameters lower tuple ⟨radius,inside⟩ mode = _
  congr 1
  change ((Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^grade *
    (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^reserve) *
    (Real.exp (radialPhase parameters radius mode.2) : ℂ) =
    (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^reserve *
      ((Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^grade *
        (Real.exp (radialPhase parameters radius mode.2) : ℂ))
  ring

def tupleConjugatedPhysicalRowCurve (row : Fin 3) (grade : ℕ) (radius : ℝ) : CellL2 1 :=
  radialConjugatedAction parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row) grade 0 radius
    (tupleConjugatedSevenCurve parameters lower tuple grade radius)

theorem tupleConjugatedPhysicalRowCurve_smooth (row : Fin 3) (grade : ℕ) :
    ContDiffOn ℝ ∞ (tupleConjugatedPhysicalRowCurve parameters length compact lower positive bounded state tuple row grade)
      (Icc lower 1) :=
  coherentConjugatedKernelCurve_smooth parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row) (tupleConjugatedSevenCurve parameters lower tuple)
    (tupleConjugatedSevenCurve_smooth parameters lower positive tuple)
    (tupleConjugatedSevenCurve_shift parameters lower tuple) grade
    (originalPhysicalRowKernel_finiteOrder parameters length compact state lower positive bounded row grade)

theorem tupleConjugatedPhysicalRowCurve_coefficient (row : Fin 3) (grade : ℕ)
    (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    tupleConjugatedPhysicalRowCurve parameters length compact lower positive bounded state tuple row grade radius.val mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        ((Real.exp (radialPhase parameters radius.val mode.2) : ℂ) •
          negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
            (tuplePhysicalRowTrace parameters length compact lower positive state tuple radius row) mode) := by
  have radiusSame : collarRadius lower positive bounded.le radius.val = tupleRadius lower positive radius := by
    apply Subtype.ext
    exact collarRadius_literal lower positive bounded.le radius.val radius.property
  unfold tupleConjugatedPhysicalRowCurve radialConjugatedAction
  rw [radiusSame]
  have original := fullNegativeKernelAction_coefficient_hasSum
    (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
    (lowPhysicalRowKernel parameters length compact state row (tupleRadius lower positive radius))
    (sevenSlotFlatten _ 0 0 (tupleNormalizedInput parameters lower positive tuple radius)) mode
  have actual : HasSum (fun shift =>
      (lowPhysicalRowKernel parameters length compact state row (tupleRadius lower positive radius)).entry shift
        (twoFrequencyTranslation shift mode)
        (originalTupleNormalizedCoefficient parameters lower tuple radius (twoFrequencyTranslation shift mode)))
      (negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
        (tuplePhysicalRowTrace parameters length compact lower positive state tuple radius row) mode) := by
    simpa only [tupleNormalizedInput_coefficient,tuplePhysicalRowTrace] using original
  have result := conjugatedKernelAction_exactCoefficient parameters grade (tupleRadius lower positive radius)
    (lowPhysicalRowKernel parameters length compact state row (tupleRadius lower positive radius)) _
    (originalTupleNormalizedCoefficient parameters lower tuple radius)
    (fun query => by simpa only [Complex.ofReal_pow,tupleRadius] using
      tupleConjugatedSevenCurve_coefficient parameters lower tuple grade radius query) mode _ actual
  simpa only [Complex.ofReal_pow,tupleRadius] using result

end Grad.AnnularOriginalCoreRealization
