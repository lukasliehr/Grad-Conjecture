import AKV24ExactPolarRowRadialCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.PhaseAlgebra Grad.AnnularSmoothCore
open Grad.AnnularOriginalSmoothCore Grad.AnnularOriginalCoreRealization Grad.AnnularCurrentSource
open Grad.AnnularCurrentLow Grad.AnnularHighTilt Grad.AnnularSourceGraph
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularReconstruction

def OriginalRowRadialCurves.of_ae {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ}
    {row target : DivisionRow dimension lower} (curves : OriginalRowRadialCurves parameters lower row)
    (same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      originalRowCoefficient parameters 0 lower target radius mode = originalRowCoefficient parameters 0 lower row radius mode) :
    OriginalRowRadialCurves parameters lower target where
  curve := curves.curve
  smooth := curves.smooth
  same grade := by
    filter_upwards [curves.same grade,same] with radius curve target
    intro mode
    rw [target mode]
    exact curve mode

def OriginalRowRadialCurves.add {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ}
    {first second : DivisionRow dimension lower}
    (a : OriginalRowRadialCurves parameters lower first) (b : OriginalRowRadialCurves parameters lower second) :
    OriginalRowRadialCurves parameters lower (first+second) where
  curve grade radius := a.curve grade radius+b.curve grade radius
  smooth grade := (a.smooth grade).add (b.smooth grade)
  same grade := by
    filter_upwards [a.same grade,b.same grade,originalRowCoefficient_add_ae parameters 0 lower first second] with radius firstSame secondSame added
    intro mode
    change a.curve grade radius mode+b.curve grade radius mode=_
    rw [firstSame mode,secondSame mode,added mode,smul_add,smul_add]

def OriginalRowRadialCurves.sub {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ}
    {first second : DivisionRow dimension lower}
    (a : OriginalRowRadialCurves parameters lower first) (b : OriginalRowRadialCurves parameters lower second) :
    OriginalRowRadialCurves parameters lower (first-second) where
  curve grade radius := a.curve grade radius-b.curve grade radius
  smooth grade := (a.smooth grade).sub (b.smooth grade)
  same grade := by
    filter_upwards [a.same grade,b.same grade,originalRowCoefficient_sub_ae parameters 0 lower first second] with radius firstSame secondSame subtracted
    intro mode
    change a.curve grade radius mode-b.curve grade radius mode=_
    rw [firstSame mode,secondSame mode,subtracted mode,smul_sub,smul_sub]

def OriginalRowRadialCurves.meanFree {parameters : PhaseParameters} {lower : ℝ}
    {row : DivisionRow 1 lower} (curves : OriginalRowRadialCurves parameters lower row) :
    OriginalRowRadialCurves parameters lower (meanFreeRow lower row) where
  curve grade radius := hilbertMeanFree parameters (curves.curve grade radius)
  smooth grade := (hilbertMeanFree parameters).restrictScalars ℝ |>.contDiff.comp_contDiffOn (curves.smooth grade)
  same grade := by
    filter_upwards [curves.same grade,originalRowCoefficient_meanFree_ae parameters 0 lower row] with radius same projected
    intro mode
    change (if mode.1=0 then (0 : ℂ) else 1) • curves.curve grade radius mode = _
    rw [same mode,projected mode]
    by_cases zero : mode.1=0 <;> simp [zero]

def OriginalRowRadialCurves.divide {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ}
    {row target : DivisionRow dimension lower} (curves : OriginalRowRadialCurves parameters lower row)
    (positive : 0 < lower)
    (same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      originalRowCoefficient parameters 0 lower target radius mode = (radius : ℂ)⁻¹ • originalRowCoefficient parameters 0 lower row radius mode) :
    OriginalRowRadialCurves parameters lower target where
  curve grade radius := (radius : ℂ)⁻¹ • curves.curve grade radius
  smooth grade := (reciprocalRadius_smooth lower positive).smul (curves.smooth grade)
  same grade := by
    filter_upwards [curves.same grade,same] with radius curve divided
    intro mode
    change (radius : ℂ)⁻¹ • curves.curve grade radius mode = _
    rw [curve mode,divided mode]
    simp only [smul_smul]
    congr 1
    ring

/-- The original BF high tilt followed by rho decoding is exactly the
manuscript's original sqrt(r) Fourier coordinate. -/
theorem originalF1Coefficient_eq_originalRow (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (row : DivisionRow 1 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      originalF1Coefficient parameters lower positive bounded.le row radius mode = originalRowCoefficient parameters 0 lower row radius mode := by
  filter_upwards [divisionHighWeight_ae lower positive bounded.le row,ae_restrict_mem measurableSet_Icc] with radius high inside
  intro mode
  have root : (Real.sqrt radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (positive.trans_le inside.1)).ne'
  have phase : (Real.exp (radialPhase parameters radius mode.2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have decoded := originalSourceStorage_decode parameters lower positive radius inside mode ((Real.sqrt radius : ℂ)⁻¹ • row mode radius)
  rw [← Complex.coe_smul,smul_inv_smul₀ root] at decoded
  unfold originalF1Coefficient lowRhoPhysicalCoefficient
  rw [high mode,decoded]
  change (Real.exp (-radialPhase parameters radius mode.2) : ℂ) • ((Real.sqrt radius : ℂ)⁻¹ • row mode radius) = _
  unfold originalRowCoefficient originalRowWeight
  simp only [pow_zero,mul_one,smul_smul,Real.exp_neg,Complex.ofReal_inv,Complex.ofReal_mul]
  congr 1
  field_simp

end Grad.AnnularGeneralSourceRegularity
