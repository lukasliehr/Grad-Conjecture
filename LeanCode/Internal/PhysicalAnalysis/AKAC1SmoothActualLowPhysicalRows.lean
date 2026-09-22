import AKV43SameObservedFullSevenSmoothness
import AKV38ExactInversePhaseRadialRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularOriginalCoreRealization Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2

/-- All original-width weighted curves of one exact completed physical row.
This packages an established property; actual consumers construct the package. -/
structure SmoothLowPhysicalRow {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (row : DivisionRow dimension lower) where
  curve : ℕ → ℝ → CellL2 dimension
  smooth : ∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1)
  same : ∀ grade, ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
    curve grade radius mode = (annularFrequency mode.1 mode.2 : ℂ)^grade •
      ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
        lowRhoPhysicalCoefficient parameters lower positive row radius mode)

theorem SmoothLowPhysicalRow.shift {dimension : ℕ} {parameters : PhaseParameters}
    {lower : ℝ} {positive : 0 < lower} {row : DivisionRow dimension lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower < 1)
    (grade reserve : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    curves.curve (grade+reserve) radius mode = (annularFrequency mode.1 mode.2 : ℂ)^reserve •
      curves.curve grade radius mode :=
  actualWeightedCurve_shift lower bounded curves.curve (fun grade => (curves.smooth grade).continuousOn)
    _ curves.same grade reserve radius inside mode

/-- Remove the one polynomial grade introduced by the actual seven-slot
normalization, while retaining every physical coefficient and source. -/
def SmoothLowPhysicalRow.of_shifted {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (row : DivisionRow dimension lower)
    (curve : ℕ → ℝ → CellL2 dimension)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1))
    (same : ∀ grade, ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      curve grade radius mode = (annularFrequency mode.1 mode.2 : ℂ)^(grade+1) •
        ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
          lowRhoPhysicalCoefficient parameters lower positive row radius mode)) :
    SmoothLowPhysicalRow parameters lower positive row where
  curve grade radius := hilbertReserve parameters dimension 1 (curve grade radius)
  smooth grade := (hilbertReserve parameters dimension 1).restrictScalars ℝ |>.contDiff.comp_contDiffOn (smooth grade)
  same grade := by
    filter_upwards [same grade] with radius actual
    intro mode
    rw [hilbertReserve_apply,actual mode]
    simp only [frequencyReserveSymbol,pow_succ,pow_zero,one_mul,mul_smul]
    rw [smul_comm ((annularFrequency mode.1 mode.2 : ℂ)^grade),inv_smul_smul₀
      (Complex.ofReal_ne_zero.mpr (annularFrequency_pos mode).ne')]

def SmoothLowPhysicalRow.action {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target)
    (regular : RegularKernelFamily kernel)
    (smoothKernel : SmoothConjugatedFamily parameters lower positive bounded.le kernel)
    {row : DivisionRow source lower} (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow parameters lower positive
      (regularRadialBulkAction parameters 0 lower positive bounded.le kernel regular row) where
  curve grade radius := radialConjugatedAction parameters lower positive bounded.le kernel grade 0 radius (curves.curve grade radius)
  smooth grade := coherentConjugatedKernelCurve_smooth parameters lower positive bounded.le kernel curves.curve curves.smooth
    (curves.shift bounded) grade (smoothKernel grade)
  same grade := radialConjugatedAction_actual parameters lower positive bounded.le kernel regular row grade (curves.curve grade) (curves.same grade)

end Grad.ActualSmoothPhysicalField
