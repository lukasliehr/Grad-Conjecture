import AJL5ActualRawSourceCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
namespace Grad.AnnularSmoothSources
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction
open Grad.SourceCollarCoefficients Grad.AnnularRadialSmoothness Grad.AnnularCurrentLow
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularKernelContinuity

/-- The polynomial insertion cancels only its own exact input denominator. -/
theorem polynomialWeightRatio_cancel (power : ℕ) (shift mode : ℤ × ℤ) :
    (polynomialWeightRatio power shift mode : ℂ) *
      (Grad.AnnularVariational.annularFrequency (twoFrequencyTranslation shift mode).1
        (twoFrequencyTranslation shift mode).2 ^ power : ℂ) =
      (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) := by
  have positive := annularFrequency_pos (twoFrequencyTranslation shift mode)
  have actual : polynomialWeightRatio power shift mode *
      Grad.SourceCollarDivision.annularFrequency (twoFrequencyTranslation shift mode).1
        (twoFrequencyTranslation shift mode).2 ^ power =
      Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 ^ power := by
    unfold polynomialWeightRatio
    exact div_mul_cancel₀ _ (pow_ne_zero _ positive.ne')
  exact_mod_cast actual

/-- Generic coefficient fidelity for any actual physical input, including
full unknown-plus-known seven packets. No finite support premise is used. -/
theorem polynomialKernelAction_exactCoefficient {source target : ℕ}
    (parameters : PhaseParameters) (power : ℕ) (kernel : FullTwoFrequencyKernel parameters source target)
    (input : CellL2 source) (physical : (ℤ × ℤ) → ComplexEuclidean source)
    (same : ∀ mode, input mode = (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) • physical mode)
    (mode : ℤ × ℤ) (output : ComplexEuclidean target)
    (actual : HasSum (fun shift => kernel.entry shift (twoFrequencyTranslation shift mode)
      (physical (twoFrequencyTranslation shift mode))) output) :
    polynomialKernelAction parameters power kernel input mode =
      (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) • output := by
  have polynomial := polynomialKernelAction_coefficient parameters power kernel input mode
  have scaled := ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
    ContinuousLinearMap.id ℂ (ComplexEuclidean target)).hasSum actual
  apply polynomial.unique
  apply scaled.congr_fun
  intro shift
  change _ = (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
    kernel.entry shift (twoFrequencyTranslation shift mode) (physical (twoFrequencyTranslation shift mode))
  rw [same, map_smul,smul_smul,polynomialWeightRatio_cancel]

/-- AE transport for any original stored bulk field and any actual regular
radial kernel, with the original phase/rho decoding unchanged. -/
theorem radialPolynomialAction_actual {source target : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target)
    (regular : RegularKernelFamily kernel) (field : DivisionRow source lower) (power : ℕ)
    (curve : ℝ → CellL2 source)
    (same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      curve radius mode = (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
        lowRhoPhysicalCoefficient parameters lower positive field radius mode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      radialPolynomialAction parameters lower positive bounded kernel power radius (curve radius) mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
          lowRhoPhysicalCoefficient parameters lower positive
            (regularRadialBulkAction parameters 0 lower positive bounded kernel regular field) radius mode := by
  filter_upwards [same,lowRegularAction_physical parameters lower positive bounded kernel regular field]
    with radius same actual
  intro mode
  exact polynomialKernelAction_exactCoefficient
    (radialKernelParameters parameters (collarRadius lower positive bounded radius)) power
    (kernel (collarRadius lower positive bounded radius)) (curve radius)
    (lowRhoPhysicalCoefficient parameters lower positive field radius) same mode _ (actual mode)

end Grad.AnnularSmoothSources
