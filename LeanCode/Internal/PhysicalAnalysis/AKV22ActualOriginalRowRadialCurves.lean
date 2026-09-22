import AKV21WeightedAngularHilbertContractions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarRestriction Grad.SourceBoundaryTrace Grad.PhaseAlgebra
open Grad.AnnularSourceGraph Grad.AnnularSmoothCore Grad.SourceCollarFullSource

/-- Exact all-grade smooth curves for one original sqrt(r)-stored source row. -/
structure OriginalRowRadialCurves {dimension : ℕ} (parameters : PhaseParameters) (lower : ℝ)
    (row : DivisionRow dimension lower) where
  curve : ℕ → ℝ → CellL2 dimension
  smooth : ∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1)
  same : ∀ grade, ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
    curve grade radius mode = (annularFrequency mode.1 mode.2 : ℂ)^grade •
      ((Real.exp (radialPhase parameters radius mode.2) : ℂ) • originalRowCoefficient parameters 0 lower row radius mode)

theorem originalRow_phase_cancel {dimension : ℕ} (parameters : PhaseParameters) (lower radius : ℝ)
    (positive : 0 < radius) (row : DivisionRow dimension lower) (mode : ℤ × ℤ) :
    (Real.exp (radialPhase parameters radius mode.2) : ℂ) • originalRowCoefficient parameters 0 lower row radius mode =
      (Real.sqrt radius : ℂ)⁻¹ • row mode radius := by
  have root : (Real.sqrt radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr positive).ne'
  have phase : (Real.exp (radialPhase parameters radius mode.2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  unfold originalRowCoefficient originalRowWeight
  simp only [pow_zero,mul_one,Complex.ofReal_mul,smul_smul]
  congr 1
  field_simp

theorem OriginalRowRadialCurves.shift {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ}
    {row : DivisionRow dimension lower} (curves : OriginalRowRadialCurves parameters lower row)
    (bounded : lower < 1) (grade reserve : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    curves.curve (grade+reserve) radius mode = (annularFrequency mode.1 mode.2 : ℂ)^reserve • curves.curve grade radius mode :=
  actualWeightedCurve_shift lower bounded curves.curve (fun grade => (curves.smooth grade).continuousOn)
    _ curves.same grade reserve radius inside mode

def cartesianOriginalRowRadialCurves {dimension : ℕ} (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : ACore parameters dimension) :
    OriginalRowRadialCurves parameters lower (cartesianWeightedRadialRow parameters lower positive bounded field 0 0) where
  curve grade := cartesianWeightedRadialCurve parameters lower positive bounded field grade 0
  smooth grade := cartesianWeightedRadialCurve_smooth parameters lower positive bounded field grade 0
  same grade := by
    have stored (mode : ℤ × ℤ) := radialToLp_ae lower
      (radialCoefficientJet (originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2))) mode.1 0)
      (radialCoefficientJet_smooth _ (originalPolarValue_smooth _) _ _).continuous
    filter_upwards [ae_all_iff.mpr stored,ae_restrict_mem measurableSet_Icc] with radius stored inside
    intro mode
    rw [cartesianWeightedRadialCurve_coefficient parameters lower positive bounded field grade 0 mode radius inside,
      originalRow_phase_cancel parameters lower radius (positive.trans_le inside.1)]
    change (annularFrequency mode.1 mode.2 : ℂ)^grade • _ =
      (annularFrequency mode.1 mode.2 : ℂ)^grade • ((Real.sqrt radius : ℂ)⁻¹ • (restrictionModeLp lower 0 0 parameters field mode) radius)
    unfold restrictionModeLp
    simp only [pow_zero,one_smul]
    rw [stored mode]
    congr 1
    exact (inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (positive.trans_le inside.1)).ne') _).symm

def OriginalRowRadialCurves.smul {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ}
    {row : DivisionRow dimension lower} (curves : OriginalRowRadialCurves parameters lower row) (scalar : ℂ) :
    OriginalRowRadialCurves parameters lower (scalar • row) where
  curve grade radius := scalar • curves.curve grade radius
  smooth grade := (curves.smooth grade).const_smul scalar
  same grade := by
    filter_upwards [curves.same grade, originalRowCoefficient_smul_ae parameters 0 lower scalar row] with radius same scaled
    intro mode
    change scalar • curves.curve grade radius mode = _
    rw [same mode,scaled mode]
    simp only [smul_smul]
    congr 1
    ring

end Grad.AnnularGeneralSourceRegularity
