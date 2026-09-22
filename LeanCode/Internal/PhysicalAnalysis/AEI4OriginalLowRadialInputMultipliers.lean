import AEI3LiteralLowBulkEmbedding

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction

def lowModeScalarFamily (lower : ℝ) (coefficient : LowAnnularMode → C(ℝ, ℝ))
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ mode radius, radius ∈ Icc lower 1 → |coefficient mode radius| ≤ bound) :
    LowModeBulk lower →L[ℂ] LowModeBulk lower :=
  complexLpTwoMap (fun mode => scalarRadialMap lower (coefficient mode) bound (bounded mode))
    bound nonnegative (fun _ field => scalarRadialMap_bound _ _ _ _ field)

theorem lowModeScalarFamily_bound (lower : ℝ) (coefficient : LowAnnularMode → C(ℝ, ℝ))
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ mode radius, radius ∈ Icc lower 1 → |coefficient mode radius| ≤ bound)
    (field : LowModeBulk lower) :
    ‖lowModeScalarFamily lower coefficient bound nonnegative bounded field‖ ≤ bound * ‖field‖ :=
  complexLpTwoMap_bound _ _ _ _ field

theorem lowModeScalarFamily_ae (lower : ℝ) (coefficient : LowAnnularMode → C(ℝ, ℝ))
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ mode radius, radius ∈ Icc lower 1 → |coefficient mode radius| ≤ bound)
    (field : LowModeBulk lower) (mode : LowAnnularMode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowModeScalarFamily lower coefficient bound nonnegative bounded field mode radius =
        coefficient mode radius • field mode radius :=
  scalarRadialMap_ae lower (coefficient mode) bound (bounded mode) (field mode)

/-- The first low coordinate is a_m*mu*xi. These are the three actual
normalized scalar inputs to the physical seven-slot reconstruction. -/
def lowInputRadiusCurve (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (mode : LowAnnularMode) : C(ℝ, ℝ) :=
  (lowAmplitude length parameters.gamma mode)⁻¹ • lowRadiusMuRatio lower length positive mode.val.2

def lowInputCellCurve (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (mode : LowAnnularMode) : C(ℝ, ℝ) :=
  (length * (lowAmplitude length parameters.gamma mode)⁻¹) • lowCellMuRatio lower length positive mode.val.2

def lowInputAngularCurve (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (mode : LowAnnularMode) : C(ℝ, ℝ) :=
  (mode.val.1 : ℝ) • lowInputRadiusCurve parameters lower length positive mode

theorem lowInputRadiusCurve_bound (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (mode : LowAnnularMode) (radius : ℝ) : |lowInputRadiusCurve parameters lower length positive mode radius| ≤ 2 := by
  change |(lowAmplitude length parameters.gamma mode)⁻¹ * lowRadiusMuRatio lower length positive mode.val.2 radius| ≤ 2
  rw [abs_mul]
  exact (mul_le_mul (lowAmplitude_inverse_bound length parameters.gamma mode)
    (lowRadiusMuRatio_bound lower length positive mode.val.2 radius) (abs_nonneg _) (by norm_num)).trans_eq (mul_one _)

theorem lowInputCellCurve_bound (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (mode : LowAnnularMode) (radius : ℝ) :
    |lowInputCellCurve parameters lower length positive mode radius| ≤ 2 * length := by
  change |(length * (lowAmplitude length parameters.gamma mode)⁻¹) * lowCellMuRatio lower length positive mode.val.2 radius| ≤ _
  rw [abs_mul, abs_mul, abs_of_pos lengthPositive]
  have first := mul_le_mul_of_nonneg_left (lowAmplitude_inverse_bound length parameters.gamma mode) lengthPositive.le
  exact (mul_le_mul first (lowCellMuRatio_bound lower length positive mode.val.2 radius)
    (abs_nonneg _) (by positivity)).trans_eq (by ring)

theorem lowInputAngularCurve_bound (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (mode : LowAnnularMode) (radius : ℝ) : |lowInputAngularCurve parameters lower length positive mode radius| ≤ 4 := by
  change |(mode.val.1 : ℝ) * lowInputRadiusCurve parameters lower length positive mode radius| ≤ 4
  rw [abs_mul]
  exact (mul_le_mul (lowMode_abs_le_two mode) (lowInputRadiusCurve_bound parameters lower length positive mode radius)
    (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

end Grad.AnnularCurrentLow
