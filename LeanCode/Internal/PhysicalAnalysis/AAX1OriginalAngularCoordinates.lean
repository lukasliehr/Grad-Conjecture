import AAQ19ExactSharpTraceConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFourSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.AnnularGrades Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem annularAngularWeight_pos (mode : HighAnnularMode) : 0 < annularAngularWeight mode := by
  unfold annularAngularWeight
  positivity

theorem annularAngularGrade_one (mode : HighAnnularMode) : annularGradeWeight 1 0 0 mode = annularAngularWeight mode := by
  simp [annularGradeWeight, sourceInsertedWeight, Grad.BoundaryKernelAction.splitTangentialWeight, annularAngularWeight]

/-- The original bulk of angular order one, stored in its literal weighted
coordinate. The decoder is the accepted injective all-grade inclusion. -/
def annularAngularDecode (lower : ℝ) : AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  annularLpDecode 1 0 0

theorem annularAngularDecode_apply (lower : ℝ) (field : AnnularBulk lower) (mode : HighAnnularMode) :
    annularAngularDecode lower field mode = ((annularAngularWeight mode)⁻¹ : ℝ) • field mode := by
  change (((annularGradeWeight 1 0 0 mode)⁻¹ : ℝ) : ℂ) • field mode = _
  rw [annularAngularGrade_one]
  rfl

theorem annularAngularDecode_injective (lower : ℝ) : Function.Injective (annularAngularDecode lower) :=
  annularLpDecode_injective 1 0 0

def annularQAngularSymbol (mode : HighAnnularMode) : ℂ :=
  -(annularDSymbol mode) * ((annularAngularWeight mode : ℂ)⁻¹)

theorem annularQAngularSymbol_bound (mode : HighAnnularMode) : ‖annularQAngularSymbol mode‖ ≤ 1 := by
  have multiplier := (highMultiplier_bounds mode.val.1 (Grad.ActualReferenceAssembly.highMode_not_low _ mode.property)).2
  have bound : ‖annularDSymbol mode‖ ≤ annularAngularWeight mode := by
    rw [annularDSymbol_norm]
    have h := mul_le_mul_of_nonneg_left multiplier (abs_nonneg (mode.val.1 : ℝ))
    unfold annularAngularWeight
    nlinarith
  rw [annularQAngularSymbol, norm_mul, norm_neg, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (annularAngularWeight_pos mode), ← div_eq_mul_inv]
  exact (div_le_one (annularAngularWeight_pos mode)).mpr bound

/-- Q=-D p, with p in the original one-higher angular bulk order. -/
def annularQFromAngularP (lower : ℝ) : AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  annularSymbolFamily lower annularQAngularSymbol 1 (by norm_num) annularQAngularSymbol_bound

theorem annularQFromAngularP_apply (lower : ℝ) (field : AnnularBulk lower) (mode : HighAnnularMode) :
    annularQFromAngularP lower field mode = -annularDSymbol mode • annularAngularDecode lower field mode := by
  rw [annularAngularDecode_apply]
  change (-(annularDSymbol mode) * (annularAngularWeight mode : ℂ)⁻¹) • field mode =
    -(annularDSymbol mode) • ((((annularAngularWeight mode)⁻¹ : ℝ) : ℂ) • field mode)
  rw [smul_smul, Complex.ofReal_inv]


theorem annularQFromAngularP_bound (lower : ℝ) (field : AnnularBulk lower) :
    ‖annularQFromAngularP lower field‖ ≤ ‖field‖ := by
  simpa only [annularQFromAngularP, one_mul] using annularSymbolFamily_bound lower annularQAngularSymbol 1 (by norm_num) annularQAngularSymbol_bound field

theorem annularQFromAngularP_right (lower : ℝ) (field : AnnularBulk lower) :
    annularQFromAngularP lower (annularAngularPMap lower field) = field := by
  apply lp.ext
  funext mode
  change (-(annularDSymbol mode) * (annularAngularWeight mode : ℂ)⁻¹) •
    ((annularAngularWeight mode : ℂ) • (-(annularDSymbol mode)⁻¹ • field mode)) = field mode
  rw [smul_smul, smul_smul]
  have weight : (annularAngularWeight mode : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (annularAngularWeight_pos mode).ne'
  have scalar : -(annularDSymbol mode) * (annularAngularWeight mode : ℂ)⁻¹ *
      (annularAngularWeight mode : ℂ) * -(annularDSymbol mode)⁻¹ = 1 := by
    field_simp [weight, annularDSymbol_ne_zero mode]
  rw [scalar, one_smul]

theorem annularQFromAngularP_left (lower : ℝ) (field : AnnularBulk lower) :
    annularAngularPMap lower (annularQFromAngularP lower field) = field := by
  apply lp.ext
  funext mode
  change (annularAngularWeight mode : ℂ) • (-(annularDSymbol mode)⁻¹ •
    ((-(annularDSymbol mode) * (annularAngularWeight mode : ℂ)⁻¹) • field mode)) = field mode
  rw [smul_smul, smul_smul]
  have weight : (annularAngularWeight mode : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (annularAngularWeight_pos mode).ne'
  have scalar : (annularAngularWeight mode : ℂ) * -(annularDSymbol mode)⁻¹ *
      (-(annularDSymbol mode) * (annularAngularWeight mode : ℂ)⁻¹) = 1 := by
    field_simp [weight, annularDSymbol_ne_zero mode]
  rw [scalar, one_smul]

end Grad.AnnularFourSource
