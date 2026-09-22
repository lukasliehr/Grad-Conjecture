import AJH15SameFullReconstructionSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff
namespace Grad.AnnularRadialSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.Ledger

theorem polynomialKernelAction_constantMatrix {source target : ℕ} (parameters : PhaseParameters)
    (power : ℕ) (matrix : ComplexEuclidean source →L[ℂ] ComplexEuclidean target) :
    polynomialKernelAction parameters power (constantMatrixKernel parameters source target matrix) =
      polynomialMatrixShift parameters power (0,0) matrix := by
  rw [polynomialKernelAction_matrixSeries parameters parameters power _
    (fun shift => if shift = (0,0) then matrix else 0) (fun _ _ => rfl)]
  rw [tsum_eq_single (0,0)]
  · rw [if_pos rfl]
  · intro shift nonzero
    rw [if_neg nonzero, map_zero]

theorem radialSevenSlotNormalization_smooth (lower : ℝ) (positive : 0 < lower) :
    ContDiffOn ℝ ∞ radialSevenSlotNormalization (Icc lower 1) := by
  have inverse : ContDiffOn ℝ ∞ (fun radius : ℝ => (radius : ℂ)⁻¹) (Icc lower 1) := by
    have realInverse : ContDiffOn ℝ ∞ (fun radius : ℝ => radius⁻¹) (Icc lower 1) :=
      contDiffOn_id.inv (fun radius inside => (positive.trans_le inside.1).ne')
    simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_inv] using
      Complex.ofRealCLM.contDiff.comp_contDiffOn realInverse
  exact (((((contDiffOn_const.add (inverse.smul contDiffOn_const)).add contDiffOn_const).add
    (inverse.smul contDiffOn_const)).add contDiffOn_const).add contDiffOn_const).add contDiffOn_const

/-- The original two reciprocal-radius input slots remain explicit. The
operator acts on the original seven inputs, with no phase or width change. -/
theorem radialSevenSlotKernel_smooth (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) :
    SmoothPolynomialFamily (source := 7) (target := 7) parameters lower positive bounded
      (fun radius => radialSevenSlotKernel parameters radius) := by
  intro power
  have smooth := ((polynomialMatrixShift parameters power (0,0) (source := 7) (target := 7)).restrictScalars ℝ).contDiff.comp_contDiffOn
    (radialSevenSlotNormalization_smooth lower positive)
  apply smooth.congr
  intro radius inside
  change polynomialKernelAction _ power (constantMatrixKernel _ 7 7 (radialSevenSlotNormalization _)) = _
  rw [polynomialKernelAction_constantMatrix]
  rw [collarRadius_literal lower positive bounded radius inside]
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext mode
  rfl

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)

/-- Exact AH20 reconstruction on both original seven-slot families. -/
theorem sameOriginalReconstruction_smooth (power : ℕ) :
    ContDiffOn ℝ ∞ (fun radius => polynomialKernelAction
      (radialKernelParameters parameters (collarRadius lower positive bounded.le radius)) power
      (radialCovariantKernel parameters L compact state.val (collarRadius lower positive bounded.le radius)
        state.property (positive.trans_le (collarRadius_lower lower positive bounded.le radius)))) (Icc lower 1) ∧
    ContDiffOn ℝ ∞ (fun radius => polynomialKernelAction
      (radialKernelParameters parameters (collarRadius lower positive bounded.le radius)) power
      (radialRotatedCovariantKernel parameters L compact state.val (collarRadius lower positive bounded.le radius)
        state.property (positive.trans_le (collarRadius_lower lower positive bounded.le radius)))) (Icc lower 1) := by
  constructor
  · exact ((radialNormalizedCovariantKernel_smooth parameters L compact state lower positive bounded).comp
      (radialSevenSlotKernel_smooth parameters lower positive bounded.le)) power
  · exact ((radialNormalizedRotatedCovariantKernel_smooth parameters L compact state lower positive bounded).comp
      (radialSevenSlotKernel_smooth parameters lower positive bounded.le)) power

end Grad.AnnularRadialSmoothness
