import AKBI22ExactOriginalDeterminantConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularOriginalCoreRealization Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalReconstruction Grad.AnnularSmoothCore
open Grad.AnnularCurrentSource Grad.AnnularHighTilt Grad.AnnularOriginalSmoothCore Grad.OriginalKernelCovariantRecovery

/-- Reuse the accepted coherent original bulk realization for a genuine
all-grade curve. This only changes its original sqrt(r)/rho storage. -/
def originalCoherentLowCurves (parameters : PhaseParameters) (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (curve : ℕ → ℝ → CellL2 1) (smooth : ∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1))
    (shift : ∀ grade radius,radius∈Icc lower 1→∀ mode,
      curve grade radius mode=(annularFrequency mode.1 mode.2 : ℂ)^grade • curve 0 radius mode) :
    (row : DivisionRow 1 lower) × SmoothLowPhysicalRow parameters lower positive row := by
  let continuous := fun grade => (smooth grade).continuousOn
  have grades : ∀ grade radius,radius∈Icc lower 1→∀ mode,
      curve grade radius mode=((annularFrequency mode.1 mode.2^grade : ℝ) : ℂ) • curve 0 radius mode := by
    simpa only [Complex.ofReal_pow] using shift
  let row := coherentOriginalBulk lower positive bounded curve continuous grades
  refine ⟨divisionHighWeight lower positive bounded.le row,⟨curve,smooth,?_⟩⟩
  intro grade
  have actual := coherentOriginalBulk_physical lower positive bounded curve continuous grades parameters
    (fun radius mode => (Real.exp (-radialPhase parameters radius.val mode.2) : ℂ) • curve 0 radius.val mode) (by
      intro radius mode
      rw [Real.exp_neg,Complex.ofReal_inv,smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')])
  filter_upwards [actual,ae_restrict_mem measurableSet_Icc] with radius actual inside
  intro mode
  change curve grade radius mode=(annularFrequency mode.1 mode.2 : ℂ)^grade •
    ((Real.exp (radialPhase parameters radius mode.2) : ℂ) • originalF1Coefficient parameters lower positive bounded.le row radius mode)
  rw [actual inside mode,Real.exp_neg,Complex.ofReal_inv,
    smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')]
  exact shift grade radius inside mode

variable {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower} {row : DivisionRow 1 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower<1) (axis : Bool)

def originalDifferentiatedCurves : (target : DivisionRow 1 lower) × SmoothLowPhysicalRow parameters lower positive target :=
  originalCoherentLowCurves parameters lower positive bounded
    (fun grade radius => hilbertFrequencyOperator parameters 1 (some axis) (curves.curve (grade+1) radius))
    (fun grade => (hilbertFrequencyOperator parameters 1 (some axis)).restrictScalars ℝ |>.contDiff.comp_contDiffOn (curves.smooth (grade+1))) (by
      intro grade radius inside mode
      rw [hilbertFrequencyOperator_apply,hilbertFrequencyOperator_apply,Nat.add_comm grade 1,
        curves.shift bounded 1 grade radius inside mode]
      exact smul_comm _ _ _)

theorem originalDifferentiatedCurves_curve (grade : ℕ) (radius : ℝ) :
    (originalDifferentiatedCurves curves bounded axis).2.curve grade radius=
      hilbertFrequencyOperator parameters 1 (some axis) (curves.curve (grade+1) radius) := rfl

theorem originalDifferentiatedCurves_negativeRotation (radius : Icc lower (1 : ℝ)) :
    originalCurveNegativeTrace (originalDifferentiatedCurves curves bounded false).2 radius=
      originalCurveNegativeRotation curves radius := rfl

theorem originalDifferentiatedCurves_negativeAxial (radius : Icc lower (1 : ℝ)) :
    originalCurveNegativeTrace (originalDifferentiatedCurves curves bounded true).2 radius=
      originalCurveNegativeAxial curves radius := rfl

end Grad.OriginalKernelHomogeneousGraph
