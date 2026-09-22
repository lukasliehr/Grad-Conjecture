import AKD4OriginalIndependentConjugatedSources
import AKC1SameConjugatedKernelAction
import AJL6ExactPolynomialPhysicalAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.PhaseAlgebra Grad.BoundaryKernelAction Grad.SourceCollarCoefficients
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularCurrentLow
open Grad.AnnularKernelContinuity Grad.AnnularSmoothSources

theorem conjugatedWeightRatio_cancel (parameters : PhaseParameters) (grade : ℕ)
    (radius : ℝ) (shift mode : ℤ × ℤ) :
    (bulkWeightRatio parameters grade radius shift mode : ℂ) *
      ((Grad.AnnularVariational.annularFrequency (twoFrequencyTranslation shift mode).1
        (twoFrequencyTranslation shift mode).2 ^ grade : ℂ) *
        (Real.exp (radialPhase parameters radius (twoFrequencyTranslation shift mode).2) : ℂ)) =
      (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℂ) *
        (Real.exp (radialPhase parameters radius mode.2) : ℂ) := by
  have nonzero := pow_ne_zero grade (Grad.SourceBoundaryTrace.annularFrequency_pos (twoFrequencyTranslation shift mode)).ne'
  have actual : bulkWeightRatio parameters grade radius shift mode *
      (Grad.SourceCollarDivision.annularFrequency (twoFrequencyTranslation shift mode).1
        (twoFrequencyTranslation shift mode).2 ^ grade *
        Real.exp (radialPhase parameters radius (twoFrequencyTranslation shift mode).2)) =
      Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 ^ grade *
        Real.exp (radialPhase parameters radius mode.2) := by
    unfold bulkWeightRatio
    rw [Real.exp_sub]
    field_simp [nonzero, Real.exp_ne_zero]
  exact_mod_cast actual

/-- Generic fidelity for the actual original-width phase-conjugated
kernel. The physical input and actual kernel entry are unchanged. -/
theorem conjugatedKernelAction_exactCoefficient {source target : ℕ}
    (parameters : PhaseParameters) (grade : ℕ) (radius : RadialPoint)
    (kernel : RadialKernel parameters radius source target)
    (input : CellL2 source) (physical : (ℤ × ℤ) → ComplexEuclidean source)
    (same : ∀ mode, input mode = (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℂ) •
      ((Real.exp (radialPhase parameters radius.val mode.2) : ℂ) • physical mode))
    (mode : ℤ × ℤ) (output : ComplexEuclidean target)
    (actual : HasSum (fun shift => kernel.entry shift (twoFrequencyTranslation shift mode)
      (physical (twoFrequencyTranslation shift mode))) output) :
    conjugatedKernelAction parameters grade 0 radius kernel input mode =
      (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℂ) •
        ((Real.exp (radialPhase parameters radius.val mode.2) : ℂ) • output) := by
  have convolution := conjugatedKernelAction_coefficient parameters grade 0 radius kernel input mode
  simp only [frequencyReserveSymbol, pow_zero, inv_one, mul_one] at convolution
  have scaled := (((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℂ) *
    (Real.exp (radialPhase parameters radius.val mode.2) : ℂ)) •
    ContinuousLinearMap.id ℂ (ComplexEuclidean target)).hasSum actual
  rw [smul_smul]
  apply convolution.unique
  apply scaled.congr_fun
  intro shift
  change _ = ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℂ) *
    (Real.exp (radialPhase parameters radius.val mode.2) : ℂ)) •
    kernel.entry shift (twoFrequencyTranslation shift mode) (physical (twoFrequencyTranslation shift mode))
  rw [same, map_smul, map_smul]
  simp only [smul_smul]
  rw [conjugatedWeightRatio_cancel]

/-- Exact AE radial fidelity for every existing stored bulk input. This
helper is also valid for the same unknown packet, without finite support. -/
theorem radialConjugatedAction_actual {source target : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target)
    (regular : RegularKernelFamily kernel) (field : DivisionRow source lower) (grade : ℕ)
    (curve : ℝ → CellL2 source)
    (same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      curve radius mode = (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℂ) •
        ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
          lowRhoPhysicalCoefficient parameters lower positive field radius mode)) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      radialConjugatedAction parameters lower positive bounded kernel grade 0 radius (curve radius) mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℂ) •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            lowRhoPhysicalCoefficient parameters lower positive
              (regularRadialBulkAction parameters 0 lower positive bounded kernel regular field) radius mode) := by
  filter_upwards [same, lowRegularAction_physical parameters lower positive bounded kernel regular field,
    ae_restrict_mem measurableSet_Icc] with radius same actual inside
  intro mode
  have literal := collarRadius_literal lower positive bounded radius inside
  have inputSame : ∀ query, curve radius query =
      (Grad.AnnularVariational.annularFrequency query.1 query.2 ^ grade : ℂ) •
        ((Real.exp (radialPhase parameters (collarRadius lower positive bounded radius).val query.2) : ℂ) •
          lowRhoPhysicalCoefficient parameters lower positive field radius query) := by
    intro query
    rw [literal]
    exact same query
  have result := conjugatedKernelAction_exactCoefficient parameters grade
    (collarRadius lower positive bounded radius) (kernel (collarRadius lower positive bounded radius))
    (curve radius) (lowRhoPhysicalCoefficient parameters lower positive field radius) inputSame mode _ (actual mode)
  simpa only [radialConjugatedAction, literal] using result

end Grad.AnnularWeightedSmoothness

namespace Grad.AnnularSmoothSources
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularWeightedSmoothness Grad.SourceCollarCoefficients
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction

theorem FiniteSmoothStoredRow.conjugatedPolynomial_shift {dimension : ℕ} {lower : ℝ}
    {field : DivisionRow dimension lower} (source : FiniteSmoothStoredRow lower field)
    (grade reserve : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    source.conjugatedPolynomial (grade + reserve) radius mode =
      (Grad.AnnularVariational.annularFrequency mode.1 mode.2 : ℂ) ^ reserve •
        source.conjugatedPolynomial grade radius mode := by
  rw [source.conjugatedPolynomial_mode, source.conjugatedPolynomial_mode, pow_add, mul_smul]
  exact smul_comm _ _ _

theorem radialConjugatedAction_finite_reserve {source target : ℕ} {lower : ℝ}
    {field : DivisionRow source lower} (finite : FiniteSmoothStoredRow lower field)
    (parameters : PhaseParameters) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target)
    (grade reserve : ℕ) (radius : ℝ) :
    radialConjugatedAction parameters lower positive bounded kernel grade reserve radius
        (finite.conjugatedPolynomial (grade + reserve) radius) =
      radialConjugatedAction parameters lower positive bounded kernel grade 0 radius
        (finite.conjugatedPolynomial grade radius) := by
  exact (conjugatedKernelAction_same parameters grade reserve
    (collarRadius lower positive bounded radius) (kernel (collarRadius lower positive bounded radius))
    _ _ (finite.conjugatedPolynomial_shift grade reserve radius)).trans
    (conjugatedKernelAction_same parameters grade 0
      (collarRadius lower positive bounded radius) (kernel (collarRadius lower positive bounded radius))
      _ _ (fun _ => by rw [pow_zero, one_smul])).symm

end Grad.AnnularSmoothSources
