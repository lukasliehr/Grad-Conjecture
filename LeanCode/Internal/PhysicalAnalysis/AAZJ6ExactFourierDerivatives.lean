import AAZJ5ClosedRadialSeriesDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularJointRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace









open Grad.AnnularRadialJets Grad.AnnularRegularity





def annularCellISymbol (mode : HighAnnularMode) : ℂ := Complex.I * ((mode.val.2 : ℝ) : ℂ)

def annularMixedSymbol (angular cell : ℕ) (mode : HighAnnularMode) : ℂ :=
  annularAngularISymbol mode ^ angular * annularCellISymbol mode ^ cell

def annularFourierCoefficient (angular cell : ℕ) (mode : HighAnnularMode) (angles : ℝ × ℝ) : ℂ :=
  cellExponential mode.val.1 angles.1 * cellExponential mode.val.2 angles.2 * annularMixedSymbol angular cell mode

theorem annularCellISymbol_bound (mode : HighAnnularMode) :
    ‖annularCellISymbol mode‖ ≤ Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
  rw [annularCellISymbol, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact annularCell_frequency_bound mode

theorem annularMixedSymbol_norm_le (angular cell : ℕ) (mode : HighAnnularMode) :
    ‖annularMixedSymbol angular cell mode‖ ≤
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ (angular + cell) := by
  rw [annularMixedSymbol, norm_mul, norm_pow, norm_pow, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (annularAngularISymbol_bound mode) angular)
    (pow_le_pow_left₀ (norm_nonneg _) (annularCellISymbol_bound mode) cell)
    (pow_nonneg (norm_nonneg _) _) (pow_nonneg (zero_le_one.trans (annularRawFrequency_one_le mode)) _)

theorem annularFourierCoefficient_norm_le (angular cell : ℕ) (mode : HighAnnularMode) (angles : ℝ × ℝ) :
    ‖annularFourierCoefficient angular cell mode angles‖ ≤
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ (angular + cell) := by
  simp only [annularFourierCoefficient, norm_mul, cellExponential_norm, one_mul]
  exact annularMixedSymbol_norm_le angular cell mode

theorem annularFourierCoefficient_continuous (angular cell : ℕ) (mode : HighAnnularMode) :
    Continuous (annularFourierCoefficient angular cell mode) :=
  (((Grad.BoundaryTrace.cellExponential_smooth mode.val.1).continuous.comp continuous_fst).mul
    ((Grad.BoundaryTrace.cellExponential_smooth mode.val.2).continuous.comp continuous_snd)).mul continuous_const

theorem annularCellExponential_hasDerivAt (mode : ℤ) (angle : ℝ) :
    HasDerivAt (cellExponential mode) ((Complex.I * (mode : ℂ)) * cellExponential mode angle) angle := by
  convert (cellExponential_hasFDerivAt mode angle).hasDerivAt using 1
  simp only [cellExponentialDerivative, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, smul_apply, Complex.ofRealCLM_apply,
    Complex.ofReal_one, smul_eq_mul, mul_one]

theorem annularFourierCoefficient_angular (angular cell : ℕ) (mode : HighAnnularMode) (polar axial : ℝ) :
    HasDerivAt (fun angle => annularFourierCoefficient angular cell mode (angle, axial))
      (annularFourierCoefficient (angular + 1) cell mode (polar, axial)) polar := by
  have differentiated := ((annularCellExponential_hasDerivAt mode.val.1 polar).mul_const
    (cellExponential mode.val.2 axial)).mul_const (annularMixedSymbol angular cell mode)
  apply differentiated.congr_deriv
  simp only [annularFourierCoefficient, annularMixedSymbol, annularAngularISymbol, pow_succ]
  push_cast
  ring

theorem annularFourierCoefficient_cell (angular cell : ℕ) (mode : HighAnnularMode) (polar axial : ℝ) :
    HasDerivAt (fun angle => annularFourierCoefficient angular cell mode (polar, angle))
      (annularFourierCoefficient angular (cell + 1) mode (polar, axial)) axial := by
  have differentiated := ((annularCellExponential_hasDerivAt mode.val.2 axial).const_mul
    (cellExponential mode.val.1 polar)).mul_const (annularMixedSymbol angular cell mode)
  apply differentiated.congr_deriv
  simp only [annularFourierCoefficient, annularMixedSymbol, annularCellISymbol, pow_succ]
  push_cast
  ring

end Grad.AnnularJointRegularity
