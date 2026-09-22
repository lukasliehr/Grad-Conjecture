import AEI11LiteralPhysicalPacketFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

theorem lowOutputScaledMap_ae (lower : ℝ) (row : Fin 2) (coefficient : LowAnnularMode → C(ℝ, ℝ))
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ mode radius, radius ∈ Icc lower 1 → |coefficient mode radius| ≤ bound)
    (scalar : ℂ) (field : DivisionRow 1 lower) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      (scalar • lowOutputMap lower row coefficient bound nonnegative bounded) field index radius =
        if index.1 = row then scalar • (coefficient index.2 radius • field index.2.val radius) else 0 := by
  filter_upwards [lowOutputMap_ae lower row coefficient bound nonnegative bounded field index,
    Lp.coeFn_smul scalar (lowOutputMap lower row coefficient bound nonnegative bounded field index)]
    with radius actual scaled
  change (scalar • lowOutputMap lower row coefficient bound nonnegative bounded field index) radius = _
  rw [scaled]
  change scalar • lowOutputMap lower row coefficient bound nonnegative bounded field index radius = _
  rw [actual]
  split_ifs <;> simp only [smul_zero]

theorem lowFirstOutput_ae (parameters : PhaseParameters) (lower length : ℝ)
    (field : DivisionRow 1 lower) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowFirstOutput parameters lower length field index radius =
        if index.1 = 0 then lowAmplitude length parameters.gamma index.2 • field index.2.val radius else 0 := by
  exact lowOutputMap_ae lower 0 (lowAmplitudeCurve parameters length) (lowBalanceConstant length parameters.gamma + 2)
    (by have balance : 1 ≤ lowBalanceConstant length parameters.gamma := le_max_left _ _; linarith)
    (fun mode radius _ => lowAmplitudeCurve_bound parameters length mode radius) field index

theorem lowCellOutput_ae (lower length : ℝ) (positive : 0 < lower)
    (field : DivisionRow 1 lower) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowCellOutput lower length positive field index radius =
        if index.1 = 1 then (-Complex.I) • (((index.2.val.2 : ℝ) / length / lowMu length radius index.2.val.2) •
          field index.2.val radius) else 0 := by
  have actual := lowOutputScaledMap_ae lower 1 (fun mode => lowCellMuRatio lower length positive mode.val.2) 1 (by norm_num)
    (fun mode radius _ => lowCellMuRatio_bound lower length positive mode.val.2 radius) (-Complex.I) field index
  filter_upwards [actual, ae_restrict_mem measurableSet_Icc] with radius actual inside
  rw [lowCellMuRatio_actual lower length positive index.2.val.2 radius inside.1] at actual
  exact actual

theorem lowAngularOutput_ae (lower length : ℝ) (positive : 0 < lower)
    (field : DivisionRow 1 lower) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowAngularOutput lower length positive field index radius =
        if index.1 = 1 then (-Complex.I) • (((index.2.val.1 : ℝ) * radius⁻¹ / lowMu length radius index.2.val.2) •
          field index.2.val radius) else 0 := by
  have actual := lowOutputScaledMap_ae lower 1 (lowOutputAngularCurve lower length positive) 2 (by norm_num)
    (fun mode radius _ => lowOutputAngularCurve_bound lower length positive mode radius) (-Complex.I) field index
  filter_upwards [actual, ae_restrict_mem measurableSet_Icc] with radius actual inside
  have coefficient : lowOutputAngularCurve lower length positive index.2 radius =
      (index.2.val.1 : ℝ) * radius⁻¹ / lowMu length radius index.2.val.2 := by
    change (index.2.val.1 : ℝ) * lowRadiusMuRatio lower length positive index.2.val.2 radius = _
    rw [lowRadiusMuRatio_actual lower length positive index.2.val.2 radius inside.1]
    ring
  rw [coefficient] at actual
  exact actual

end Grad.AnnularCurrentLow
