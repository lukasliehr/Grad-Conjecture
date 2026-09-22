import AKCX31ActualKnownAllSpatialGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.SpatialMultiplier Grad.CellWeights

/-- Internal finite cell reserve for the actual phase and its spatial derivatives. -/
structure StartupCellSpatialSymbol (order reserve : ℕ) where
  toFun : ℤ → Spatial → ℝ
  smooth : ∀ cell, ContDiff ℝ ∞ (toFun cell)
  bound : JetIndex order → ℝ
  nonnegative : ∀ index, 0 ≤ bound index
  derivative_bound : ∀ index cell point,
    |scalarDerivative index.val (toFun cell) point| ≤ bound index * cellWeight cell ^ reserve

namespace StartupCellSpatialSymbol
variable {order reserve dimension : ℕ} (symbol : StartupCellSpatialSymbol order reserve)

def fixed (cell : ℤ) : Symbol order openUnitDisk where
  toFun := symbol.toFun cell
  smooth := symbol.smooth cell
  bound index := ⟨symbol.bound index * cellWeight cell ^ reserve,
    mul_nonneg (symbol.nonnegative index) (pow_nonneg (cellWeight_pos cell).le _)⟩
  derivative_bound index point _ := symbol.derivative_bound index cell point

def normalized (index : JetIndex order) (cell : ℤ) (point : Spatial) : ℝ :=
  scalarDerivative index.val (symbol.toFun cell) point / cellWeight cell ^ reserve

theorem normalized_bound (index : JetIndex order) (cell : ℤ) (point : Spatial) :
    |symbol.normalized index cell point| ≤ symbol.bound index := by
  rw [normalized,abs_div,abs_of_pos (pow_pos (cellWeight_pos cell) _)]
  exact (div_le_iff₀ (pow_pos (cellWeight_pos cell) _)).mpr (symbol.derivative_bound index cell point)

theorem normalized_measurable (index : JetIndex order) (cell : ℤ) :
    AEStronglyMeasurable (symbol.normalized index cell) (volume.restrict openUnitDisk) :=
  ((scalarDerivative_smooth index.val (symbol.toFun cell) (symbol.smooth cell)).div_const _).continuous.aestronglyMeasurable

def piece (index : JetIndex order) (field : StartupL2 dimension) : StartupL2 dimension :=
  startupMomentDiagonalField (symbol.normalized index) (symbol.bound index) (symbol.nonnegative index)
    (symbol.normalized_bound index) (symbol.normalized_measurable index) field

theorem piece_same (index lower : JetIndex order) (field : GraphGrade dimension order reserve openUnitDisk) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      symbol.piece index (field.val lower) point cell =
        (scalarDerivative index.val (symbol.toFun cell) point : ℂ) •
          Realization.recoveredDerivative dimension order openUnitDisk (fun _ => reserve) lower field point cell := by
  filter_upwards [startupMomentDiagonalField_ae (symbol.normalized index) (symbol.bound index) (symbol.nonnegative index)
      (symbol.normalized_bound index) (symbol.normalized_measurable index) (field.val lower),
    Realization.recoveredDerivative_positive_coordinates dimension order openUnitDisk (fun _ => reserve) lower field]
    with point same positive
  intro cell
  change startupMomentDiagonalField _ _ _ _ _ _ point cell = _
  rw [same cell,positive cell,smul_smul]
  congr 1
  change ((scalarDerivative index.val (symbol.toFun cell) point / cellWeight cell ^ reserve : ℝ) : ℂ) *
    (cellWeight cell ^ reserve : ℂ) = _
  rw [← Complex.ofReal_pow,← Complex.ofReal_mul,div_mul_cancel₀ _ (pow_ne_zero _ (cellWeight_pos cell).ne')]

/-- SAME per-cell comparison with the accepted scalar Leibniz operator. -/
theorem piece_fixed_pairing (index lower : JetIndex order)
    (field : GraphGrade dimension order reserve openUnitDisk)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction openUnitDisk) :
    testPairing dimension openUnitDisk cell vector test (symbol.piece index (field.val lower)) =
      testPairing dimension openUnitDisk cell vector test
        (fieldMultiplier dimension openUnitDisk openUnitDisk_isOpen (derivativeScalar (symbol.fixed cell) index)
          (Realization.recoveredDerivative dimension order openUnitDisk (fun _ => reserve) lower field)) := by
  rw [testPairing_apply,testPairing_apply]
  apply integral_congr_ae
  filter_upwards [symbol.piece_same index lower field,
    fieldMultiplier_ae dimension openUnitDisk openUnitDisk_isOpen (derivativeScalar (symbol.fixed cell) index)
      (Realization.recoveredDerivative dimension order openUnitDisk (fun _ => reserve) lower field)] with point same fixedSame
  rw [same cell,fixedSame cell]
  rfl

end StartupCellSpatialSymbol
end Grad.CartesianStartup
