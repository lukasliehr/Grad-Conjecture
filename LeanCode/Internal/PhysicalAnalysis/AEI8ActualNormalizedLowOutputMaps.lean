import AEI7ActualLowOutputRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction

def lowOutputMap (lower : ℝ) (row : Fin 2) (coefficient : LowAnnularMode → C(ℝ, ℝ))
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ mode radius, radius ∈ Icc lower 1 → |coefficient mode radius| ≤ bound) :
    DivisionRow 1 lower →L[ℂ] LowEnergyBulk lower :=
  (lowRowIntoBulk lower row).toContinuousLinearMap.comp
    ((lowModeScalarFamily lower coefficient bound nonnegative bounded).comp (lowFullRestriction lower))

theorem lowOutputMap_bound (lower : ℝ) (row : Fin 2) (coefficient : LowAnnularMode → C(ℝ, ℝ))
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ mode radius, radius ∈ Icc lower 1 → |coefficient mode radius| ≤ bound)
    (field : DivisionRow 1 lower) : ‖lowOutputMap lower row coefficient bound nonnegative bounded field‖ ≤ bound * ‖field‖ := by
  change ‖lowRowIntoBulk lower row (lowModeScalarFamily lower coefficient bound nonnegative bounded (lowFullRestriction lower field))‖ ≤ _
  rw [(lowRowIntoBulk lower row).norm_map]
  exact (lowModeScalarFamily_bound _ _ _ _ _ _).trans
    (mul_le_mul_of_nonneg_left (lowFullRestrictionValue_bound lower field) nonnegative)

theorem lowOutputMap_ae (lower : ℝ) (row : Fin 2) (coefficient : LowAnnularMode → C(ℝ, ℝ))
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ mode radius, radius ∈ Icc lower 1 → |coefficient mode radius| ≤ bound)
    (field : DivisionRow 1 lower) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowOutputMap lower row coefficient bound nonnegative bounded field index radius =
        if index.1 = row then coefficient index.2 radius • field index.2.val radius else 0 := by
  change ∀ᵐ radius ∂volume.restrict (Icc lower 1),
    (if index.1 = row then lowModeScalarFamily lower coefficient bound nonnegative bounded
      (lowFullRestriction lower field) index.2 else 0) radius = _
  by_cases same : index.1 = row
  · simp only [same, if_true]
    exact lowModeScalarFamily_ae lower coefficient bound nonnegative bounded (lowFullRestriction lower field) index.2
  · simp only [same, if_false]
    exact Lp.coeFn_zero (ComplexEuclidean 1) 2 (volume.restrict (Icc lower 1))

def lowAmplitudeCurve (parameters : PhaseParameters) (length : ℝ) (mode : LowAnnularMode) : C(ℝ, ℝ) :=
  ContinuousMap.const ℝ (lowAmplitude length parameters.gamma mode)

theorem lowAmplitudeCurve_bound (parameters : PhaseParameters) (length : ℝ) (mode : LowAnnularMode) (radius : ℝ) :
    |lowAmplitudeCurve parameters length mode radius| ≤ lowBalanceConstant length parameters.gamma + 2 := by
  change |lowAmplitude length parameters.gamma mode| ≤ _
  rw [abs_of_pos (lowAmplitude_pos length parameters.gamma mode)]
  exact lowAmplitude_upper length parameters.gamma mode

def lowOutputAngularCurve (lower length : ℝ) (positive : 0 < lower) (mode : LowAnnularMode) : C(ℝ, ℝ) :=
  (mode.val.1 : ℝ) • lowRadiusMuRatio lower length positive mode.val.2

theorem lowOutputAngularCurve_bound (lower length : ℝ) (positive : 0 < lower) (mode : LowAnnularMode) (radius : ℝ) :
    |lowOutputAngularCurve lower length positive mode radius| ≤ 2 := by
  change |(mode.val.1 : ℝ) * lowRadiusMuRatio lower length positive mode.val.2 radius| ≤ 2
  rw [abs_mul]
  exact (mul_le_mul (lowMode_abs_le_two mode) (lowRadiusMuRatio_bound lower length positive mode.val.2 radius)
    (abs_nonneg _) (by norm_num)).trans_eq (mul_one _)

/-- First physical row after division of w1' by the output mu. -/
def lowFirstOutput (parameters : PhaseParameters) (lower length : ℝ) : DivisionRow 1 lower →L[ℂ] LowEnergyBulk lower :=
  lowOutputMap lower 0 (lowAmplitudeCurve parameters length) (lowBalanceConstant length parameters.gamma + 2)
    (by have := (le_max_left 1 (max (16 / (parameters.gamma * length)) (16 / lowEta length parameters.gamma))); change 0 ≤ max 1 _ + 2; linarith)
    (fun mode radius _ => lowAmplitudeCurve_bound parameters length mode radius)

/-- The axial derivative acts on the whole output, including coefficients. -/
def lowCellOutput (lower length : ℝ) (positive : 0 < lower) : DivisionRow 1 lower →L[ℂ] LowEnergyBulk lower :=
  (-Complex.I) • lowOutputMap lower 1 (fun mode => lowCellMuRatio lower length positive mode.val.2) 1 (by norm_num)
    (fun mode radius _ => lowCellMuRatio_bound lower length positive mode.val.2 radius)

/-- The angular derivative likewise acts on the actual low output. -/
def lowAngularOutput (lower length : ℝ) (positive : 0 < lower) : DivisionRow 1 lower →L[ℂ] LowEnergyBulk lower :=
  (-Complex.I) • lowOutputMap lower 1 (lowOutputAngularCurve lower length positive) 2 (by norm_num)
    (fun mode radius _ => lowOutputAngularCurve_bound lower length positive mode radius)

theorem lowFirstOutput_bound (parameters : PhaseParameters) (lower length : ℝ) (field : DivisionRow 1 lower) :
    ‖lowFirstOutput parameters lower length field‖ ≤ (lowBalanceConstant length parameters.gamma + 2) * ‖field‖ :=
  lowOutputMap_bound _ _ _ _ _ _ field

theorem lowCellOutput_bound (lower length : ℝ) (positive : 0 < lower) (field : DivisionRow 1 lower) :
    ‖lowCellOutput lower length positive field‖ ≤ ‖field‖ := by
  unfold lowCellOutput
  rw [smul_apply, norm_smul, norm_neg, Complex.norm_I, one_mul]
  exact (lowOutputMap_bound _ _ _ _ _ _ field).trans_eq (one_mul _)

theorem lowAngularOutput_bound (lower length : ℝ) (positive : 0 < lower) (field : DivisionRow 1 lower) :
    ‖lowAngularOutput lower length positive field‖ ≤ 2 * ‖field‖ := by
  unfold lowAngularOutput
  rw [smul_apply, norm_smul, norm_neg, Complex.norm_I, one_mul]
  exact lowOutputMap_bound _ _ _ _ _ _ field

end Grad.AnnularCurrentLow
