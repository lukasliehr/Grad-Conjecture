import AJU3PhysicalJetPrimitive
import AAZJ6ExactFourierDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff Interval ENNReal BigOperators
namespace Grad.AnnularPhysicalFourier
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularSmoothCore Grad.SourceCollarCoefficients
open Grad.AnnularJointRegularity Grad.AnnularRegularity

/-- Actual all-mode continuous physical jets, with their genuine primitive
law and uniform polynomial Fourier summability. -/
structure PhysicalFourierJet (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) where
  sections : ℕ → (ℤ × ℤ) → RadialContinuousSection 1 lower
  derivative : ∀ order mode, AnnularSectionDerivative lower positive bounded.le
    (sections order mode) (sections (order + 1) mode)
  summable : ∀ order grade, Summable (fun mode : ℤ × ℤ =>
    Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade * ‖sections order mode‖)

/-- The jet carrier is derived from the actual smooth Hilbert curves; none
of its derivative or convergence laws is an assumption on the solution. -/
def physicalJetOfHilbert (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (curve : ℕ → ℝ → CellL2 1)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1))
    (same : ∀ grade radius, radius ∈ Icc lower 1 → ∀ mode : ℤ × ℤ,
      curve grade radius mode =
        ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • curve 0 radius mode) :
    PhysicalFourierJet lower positive bounded where
  sections order mode := hilbertRadialJetSection lower bounded curve smooth order 0 mode
  derivative order mode := hilbertRadialJetSection_primitive lower positive bounded curve smooth order 0 mode
  summable order grade := hilbertRadialJetSection_weighted_summable lower bounded curve smooth same order grade

def physicalAngularISymbol (mode : ℤ × ℤ) : ℂ := Complex.I * ((mode.1 : ℝ) : ℂ)

theorem physicalAngularISymbol_bound (mode : ℤ × ℤ) :
    ‖physicalAngularISymbol mode‖ ≤ Grad.AnnularVariational.annularFrequency mode.1 mode.2 := by
  rw [physicalAngularISymbol, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold Grad.AnnularVariational.annularFrequency
  linarith [abs_nonneg (mode.1 : ℝ), abs_nonneg (mode.2 : ℝ)]

def physicalCellISymbol (mode : (ℤ × ℤ)) : ℂ := Complex.I * ((mode.2 : ℝ) : ℂ)

def physicalMixedSymbol (angular cell : ℕ) (mode : (ℤ × ℤ)) : ℂ :=
  physicalAngularISymbol mode ^ angular * physicalCellISymbol mode ^ cell

def physicalFourierCoefficient (angular cell : ℕ) (mode : (ℤ × ℤ)) (angles : ℝ × ℝ) : ℂ :=
  cellExponential mode.1 angles.1 * cellExponential mode.2 angles.2 * physicalMixedSymbol angular cell mode

theorem physicalCellISymbol_bound (mode : (ℤ × ℤ)) :
    ‖physicalCellISymbol mode‖ ≤ Grad.AnnularVariational.annularFrequency mode.1 mode.2 := by
  rw [physicalCellISymbol, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold Grad.AnnularVariational.annularFrequency
  linarith [abs_nonneg (mode.1 : ℝ), abs_nonneg (mode.2 : ℝ)]

theorem physicalMixedSymbol_norm_le (angular cell : ℕ) (mode : (ℤ × ℤ)) :
    ‖physicalMixedSymbol angular cell mode‖ ≤
      (Grad.AnnularVariational.annularFrequency mode.1 mode.2) ^ (angular + cell) := by
  rw [physicalMixedSymbol, norm_mul, norm_pow, norm_pow, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (physicalAngularISymbol_bound mode) angular)
    (pow_le_pow_left₀ (norm_nonneg _) (physicalCellISymbol_bound mode) cell)
    (pow_nonneg (norm_nonneg _) _) (pow_nonneg (by unfold Grad.AnnularVariational.annularFrequency; positivity) _)

theorem physicalFourierCoefficient_norm_le (angular cell : ℕ) (mode : (ℤ × ℤ)) (angles : ℝ × ℝ) :
    ‖physicalFourierCoefficient angular cell mode angles‖ ≤
      (Grad.AnnularVariational.annularFrequency mode.1 mode.2) ^ (angular + cell) := by
  simp only [physicalFourierCoefficient, norm_mul, cellExponential_norm, one_mul]
  exact physicalMixedSymbol_norm_le angular cell mode

theorem physicalFourierCoefficient_continuous (angular cell : ℕ) (mode : (ℤ × ℤ)) :
    Continuous (physicalFourierCoefficient angular cell mode) :=
  (((Grad.BoundaryTrace.cellExponential_smooth mode.1).continuous.comp continuous_fst).mul
    ((Grad.BoundaryTrace.cellExponential_smooth mode.2).continuous.comp continuous_snd)).mul continuous_const

theorem physicalFourierCoefficient_angular (angular cell : ℕ) (mode : (ℤ × ℤ)) (polar axial : ℝ) :
    HasDerivAt (fun angle => physicalFourierCoefficient angular cell mode (angle, axial))
      (physicalFourierCoefficient (angular + 1) cell mode (polar, axial)) polar := by
  have differentiated := ((annularCellExponential_hasDerivAt mode.1 polar).mul_const
    (cellExponential mode.2 axial)).mul_const (physicalMixedSymbol angular cell mode)
  apply differentiated.congr_deriv
  simp only [physicalFourierCoefficient, physicalMixedSymbol, physicalAngularISymbol, pow_succ]
  push_cast
  ring

theorem physicalFourierCoefficient_cell (angular cell : ℕ) (mode : (ℤ × ℤ)) (polar axial : ℝ) :
    HasDerivAt (fun angle => physicalFourierCoefficient angular cell mode (polar, angle))
      (physicalFourierCoefficient angular (cell + 1) mode (polar, axial)) axial := by
  have differentiated := ((annularCellExponential_hasDerivAt mode.2 axial).const_mul
    (cellExponential mode.1 polar)).mul_const (physicalMixedSymbol angular cell mode)
  apply differentiated.congr_deriv
  simp only [physicalFourierCoefficient, physicalMixedSymbol, physicalCellISymbol, pow_succ]
  push_cast
  ring

end Grad.AnnularPhysicalFourier
