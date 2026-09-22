import AKAW8SameNativeCellCarrier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularVariational

private theorem lowModeScalarFamily_scaled (lower : ℝ)
    (coefficient : LowAnnularMode → C(ℝ, ℝ)) (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ mode radius, radius ∈ Icc lower 1 → |coefficient mode radius| ≤ bound)
    (first second : LowModeBulk lower) (scale : LowAnnularMode → ℂ)
    (same : ∀ mode, second mode = scale mode • first mode) (mode : LowAnnularMode) :
    lowModeScalarFamily lower coefficient bound nonnegative bounded second mode =
      scale mode • lowModeScalarFamily lower coefficient bound nonnegative bounded first mode := by
  change scalarRadialMap lower (coefficient mode) bound (bounded mode) (second mode) =
    scale mode • scalarRadialMap lower (coefficient mode) bound (bounded mode) (first mode)
  rw [same mode,map_smul]

private theorem lowBulkSlot_scaled {dimension : ℕ} (lower : ℝ) (slot : Fin dimension)
    (first second : LowModeBulk lower) (scale : ℤ × ℤ → ℂ)
    (same : ∀ mode, second mode = scale mode.val • first mode) (mode : ℤ × ℤ) :
    lowBulkSlot lower slot second mode = scale mode • lowBulkSlot lower slot first mode := by
  change radialMatrixUnit lower slot 0 (lowBulkIntoFull lower second mode) =
    scale mode • radialMatrixUnit lower slot 0 (lowBulkIntoFull lower first mode)
  by_cases retained : |mode.1| = 1 ∨ |mode.1| = 2
  · rw [lowBulkIntoFull_retained lower second ⟨mode,retained⟩,lowBulkIntoFull_retained lower first ⟨mode,retained⟩,
      same ⟨mode,retained⟩,map_smul]
  · rw [lowBulkIntoFull_outside lower second mode retained,lowBulkIntoFull_outside lower first mode retained,map_zero,smul_zero]

/-- Every original low stored mode is multiplied by its literal insertion,
including the compulsory radial and cell normalization factors. -/
theorem lowSevenPacket_scaled (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (first second : LowEnergyBulk lower) (scale : ℤ × ℤ → ℂ)
    (same : ∀ index : LowAnnularIndex, second index = scale index.2.val • first index) (mode : ℤ × ℤ) :
    lowNormalizedSevenInput parameters lower length lengthPositive positive second mode =
      scale mode • lowNormalizedSevenInput parameters lower length lengthPositive positive first mode := by
  have component (slot : Fin 2) (index : LowAnnularMode) : lowComponent lower slot second index =
      scale index.val • lowComponent lower slot first index := same (slot,index)
  have radial (index : LowAnnularMode) : lowNormalizedRadius parameters lower length positive second index =
      scale index.val • lowNormalizedRadius parameters lower length positive first index :=
    lowModeScalarFamily_scaled lower (lowInputRadiusCurve parameters lower length positive) 2 (by norm_num)
      (fun mode radius _ => lowInputRadiusCurve_bound parameters lower length positive mode radius) _ _ _ (component 0) index
  have angular (index : LowAnnularMode) : lowNormalizedAngular parameters lower length positive second index =
      scale index.val • lowNormalizedAngular parameters lower length positive first index := by
    have scaled := lowModeScalarFamily_scaled lower (lowInputAngularCurve parameters lower length positive) 4 (by norm_num)
      (fun mode radius _ => lowInputAngularCurve_bound parameters lower length positive mode radius) _ _ _ (component 0) index
    exact (congrArg (fun value : RadialL2 1 lower => Complex.I • value) scaled).trans (smul_comm Complex.I (scale index.val) _)
  have cell (index : LowAnnularMode) : lowNormalizedCell parameters lower length lengthPositive positive second index =
      scale index.val • lowNormalizedCell parameters lower length lengthPositive positive first index := by
    have scaled := lowModeScalarFamily_scaled lower (lowInputCellCurve parameters lower length positive) (2 * length) (by positivity)
      (fun mode radius _ => lowInputCellCurve_bound parameters lower length lengthPositive positive mode radius) _ _ _ (component 0) index
    exact (congrArg (fun value : RadialL2 1 lower => Complex.I • value) scaled).trans (smul_comm Complex.I (scale index.val) _)
  change lowBulkSlot lower (0 : Fin 7) (lowComponent lower 1 second) mode +
      lowBulkSlot lower (1 : Fin 7) (lowNormalizedAngular parameters lower length positive second) mode +
      lowBulkSlot lower (2 : Fin 7) (lowNormalizedCell parameters lower length lengthPositive positive second) mode +
      lowBulkSlot lower (3 : Fin 7) (lowNormalizedRadius parameters lower length positive second) mode = _
  rw [lowBulkSlot_scaled lower 0 _ _ scale (component 1) mode,
    lowBulkSlot_scaled lower 1 _ _ scale angular mode,lowBulkSlot_scaled lower 2 _ _ scale cell mode,
    lowBulkSlot_scaled lower 3 _ _ scale radial mode,← smul_add,← smul_add,← smul_add]
  rfl

end Grad.ActualNativeCellMoments
