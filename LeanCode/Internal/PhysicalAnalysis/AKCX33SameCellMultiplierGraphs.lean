import AKCX32ActualCellSpatialMultipliers

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.SpatialMultiplier Grad.CellWeights Grad.WeakTesting.Commutation
namespace StartupCellSpatialSymbol
variable {order reserve dimension : ℕ} (symbol : StartupCellSpatialSymbol order reserve)

def baseField (field : GraphGrade dimension order reserve openUnitDisk) : StartupL2 dimension :=
  symbol.piece (zeroIndex order) (field.val (zeroIndex order))

def coordinateField (field : GraphGrade dimension order reserve openUnitDisk)
    (upper : JetIndex order) : StartupL2 dimension :=
  ∑ lower ∈ below upper, (binomial upper lower : ℂ) •
    symbol.piece (difference upper lower) (field.val lower)

theorem coordinateField_zero (field : GraphGrade dimension order reserve openUnitDisk) :
    symbol.coordinateField field (zeroIndex order) = symbol.baseField field := by
  rw [coordinateField,below_zero,Finset.sum_singleton,binomial_self,difference_self]
  simp only [Nat.cast_one,one_smul]
  rfl

theorem baseField_same (field : GraphGrade dimension order reserve openUnitDisk) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      symbol.baseField field point cell = (symbol.toFun cell point : ℂ) •
        base dimension order openUnitDisk (fun _ => reserve) field point cell :=
  symbol.piece_same (zeroIndex order) (zeroIndex order) field

theorem coordinateField_fixed_pairing (field : GraphGrade dimension order reserve openUnitDisk)
    (upper : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction openUnitDisk) :
    testPairing dimension openUnitDisk cell vector test (symbol.coordinateField field upper) =
      testPairing dimension openUnitDisk cell vector test
        (unweightedCoordinate dimension order openUnitDisk openUnitDisk_isOpen (symbol.fixed cell)
          (fun _ => reserve) upper field) := by
  rw [coordinateField,unweightedCoordinate_apply,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro lower _
  rw [map_smul,map_smul,symbol.piece_fixed_pairing]

theorem coordinateField_weak (field : GraphGrade dimension order reserve openUnitDisk)
    (upper : JetIndex order) :
    HasWeakOrderedDerivative dimension openUnitDisk (degree upper) (derivativeWord upper)
      (symbol.baseField field) (symbol.coordinateField field upper) := by
  intro cell vector test smooth compact supported
  let testing : TestFunction openUnitDisk := ⟨test,smooth,compact,supported⟩
  change testPairing dimension openUnitDisk cell vector testing (symbol.coordinateField field upper) =
    (-1 : ℂ)^degree upper * derivativeTestPairing dimension order openUnitDisk upper cell vector testing (symbol.baseField field)
  rw [symbol.coordinateField_fixed_pairing,unweightedCoordinate_weak,derivativeTestPairing_apply,derivativeTestPairing_apply]
  congr 1
  apply integral_congr_ae
  filter_upwards [symbol.baseField_same field,
    fieldMultiplier_ae dimension openUnitDisk openUnitDisk_isOpen (derivativeScalar (symbol.fixed cell) (zeroIndex order))
      (base dimension order openUnitDisk (fun _ => reserve) field)] with point same fixedSame
  rw [same cell,fixedSame cell]
  rfl

def graph (field : GraphGrade dimension order reserve openUnitDisk) : GraphGrade dimension order 0 openUnitDisk :=
  startupGraphFromWeak (symbol.baseField field) (symbol.coordinateField field)
    (symbol.coordinateField_zero field) (symbol.coordinateField_weak field)

theorem graph_base (field : GraphGrade dimension order reserve openUnitDisk) :
    base dimension order openUnitDisk (fun _ => 0) (symbol.graph field) = symbol.baseField field :=
  startupGraphFromWeak_base _ _ _ _

/-- Actual jointly square-integrable spatial product, from a finite input cell reserve. -/
theorem graph_exists (field : GraphGrade dimension order reserve openUnitDisk)
    (product : StartupL2 dimension)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      product point cell = (symbol.toFun cell point : ℂ) •
        base dimension order openUnitDisk (fun _ => reserve) field point cell) :
    ∃ output : GraphGrade dimension order 0 openUnitDisk,
      base dimension order openUnitDisk (fun _ => 0) output = product := by
  refine ⟨symbol.graph field,?_⟩
  rw [symbol.graph_base]
  apply Lp.ext
  filter_upwards [symbol.baseField_same field,same] with point one two
  apply lp.ext
  funext cell
  exact (one cell).trans (two cell).symm

end StartupCellSpatialSymbol
end Grad.CartesianStartup
