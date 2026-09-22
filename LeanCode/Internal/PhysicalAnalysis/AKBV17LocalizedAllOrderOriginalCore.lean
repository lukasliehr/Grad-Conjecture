import AKBV16LocalizedNativeCellAgreement

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.CartesianStartup
open Grad.WeightedJets Grad.BoundaryTrace Grad.SourceCollarDivision Grad.ActualSmoothPhysicalField

theorem weightedSmoothEquiv_angularCell {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (point : ClosedDisk) (cell : ℤ) :
    angularCoefficient (fun axial => (weightedSmoothEquiv parameters core).value (point,(axial : CellCircle))) cell =
      cartesianWeight parameters cell point.val • (core.val cell).value point := by
  calc
    _ = fourierCoeff (fun circle => (weightedSmoothEquiv parameters core).value (point,circle)) cell :=
      angularCoefficient_circle _ cell
    _ = diskCellFourierValue (weightedSmoothEquiv parameters core).value cell point :=
      (diskCellFourierValue_apply _ cell point).symm
    _ = _ := by
      change (diskCellFourierCoefficientJet (weightedSmoothEquiv parameters core) cell).value point = _
      rw [diskCellFourierCoefficientJet_weightedSmoothEquiv]
      rfl

/-- All-order weak regularity of the SAME localized scaled field, together with its already smooth native outer collar, recovers the actual original analytic core on the entire punctured closed disk. -/
theorem localizedAllOrder_sameOriginalCore {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (row : DivisionRow dimension lower) (curves : SmoothLowPhysicalRow parameters lower positive row)
    (scale upper : ℝ) (scalePositive : 0 < scale) (lowerUpper : lower < upper)
    (upperScale : upper ≤ scale) (upperOne : upper ≤ 1)
    (field : StartupL2 dimension) (jets : ∀ grade, GraphGrade dimension grade grade openUnitDisk)
    (sameBase : ∀ grade, base dimension grade openUnitDisk (fun _ => grade) (jets grade) = field)
    (raw : ℤ → SpatialPlane → ComplexEuclidean dimension)
    (continuousRaw : ∀ cell, ContinuousOn (raw cell) {point | 0 < ‖point‖ ∧ ‖point‖ < 1})
    (nativeSame : ∀ (point : SpatialPlane), ‖point‖ ∈ Icc lower 1 → ∀ cell : ℤ,
      raw cell point = angularCoefficient (fun axial => curves.cartesianField bounded (point,axial)) cell)
    (cutoff : SpatialPlane → ℝ) (cutoffOne : ∀ point, scale * ‖point‖ < upper → cutoff point = 1)
    (sameRaw : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      field point cell = cutoff point • (cartesianWeight parameters cell (scale • point) • raw cell (scale • point))) :
    ∃ core : ACore parameters dimension, ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ cell : ℤ,
      (core.val cell).value point = raw cell point.val := by
  obtain ⟨weighted,sameWeighted⟩ := allDiagonalGraphs_sameWeightedClosedJet parameters field jets sameBase
  have localCells := localizedWeightedCells_pointwise parameters scale upper scalePositive upperScale upperOne
    field weighted sameWeighted raw continuousRaw cutoff cutoffOne sameRaw
  have overlapCells (point : SpatialPlane) (inside : ‖point‖ ∈ Ioo lower upper) (cell : ℤ) :
      (diskCellFourierCoefficientJet weighted cell).value
        (inverseScaledDiskPoint scale scalePositive point (inside.2.le.trans upperScale)) =
      cartesianWeight parameters cell point •
        angularCoefficient (fun axial => curves.cartesianField bounded (point,axial)) cell := by
    exact (localCells point ⟨positive.trans inside.1,inside.2⟩ cell).trans
      (congrArg (cartesianWeight parameters cell point • ·) (nativeSame point ⟨inside.1.le,inside.2.le.trans upperOne⟩ cell))
  have agree := rescaledWeightedInterior_same_native curves bounded weighted scale scalePositive upper upperOne upperScale overlapCells
  let join := (lower+upper)/2
  have below : lower < join := by dsimp [join]; linarith
  have above : join < upper := by dsimp [join]; linarith
  let core := gluedWeightedOriginalCore lower join upper below above (rescaledWeightedInterior weighted scale)
    (nativeWeightedOuter curves bounded) agree parameters (rescaledWeightedInterior_smooth weighted scale)
    (nativeWeightedOuter_smooth curves bounded) (rescaledWeightedInterior_periodic weighted scale)
    (nativeWeightedOuter_periodic curves bounded)
  have literal (point : ClosedDisk) (axial : ℝ) :
      (weightedSmoothEquiv parameters core).value (point,(axial : CellCircle)) =
        gluedWeightedCylinder join (rescaledWeightedInterior weighted scale) (nativeWeightedOuter curves bounded)
          (assembleSpatialCell point.val axial) :=
    gluedWeightedOriginalCore_actual lower join upper below above _ _ agree parameters
      (rescaledWeightedInterior_smooth weighted scale) (nativeWeightedOuter_smooth curves bounded)
      (rescaledWeightedInterior_periodic weighted scale) (nativeWeightedOuter_periodic curves bounded) point axial
  refine ⟨core,?_⟩
  intro point nonzero cell
  have weightedEquality : cartesianWeight parameters cell point.val • (core.val cell).value point =
      cartesianWeight parameters cell point.val • raw cell point.val := by
    rw [← weightedSmoothEquiv_angularCell parameters core point cell]
    simp_rw [literal point]
    by_cases small : ‖point.val‖ ≤ join
    · simp only [gluedWeightedCylinder,planarPart_assembleSpatialCell,if_pos small]
      have inside : ‖point.val‖ ∈ Ioo 0 upper := ⟨nonzero,small.trans_lt above⟩
      rw [rescaledWeightedInterior_cell weighted scale scalePositive point.val (inside.2.le.trans upperScale)]
      exact localCells point.val inside cell
    · simp only [gluedWeightedCylinder,planarPart_assembleSpatialCell,if_neg small]
      have inside : ‖point.val‖ ∈ Icc lower 1 := ⟨(below.trans (lt_of_not_ge small)).le,point.property⟩
      rw [nativeWeightedOuter_cell curves bounded point.val inside,← nativeSame point.val inside cell]
  have cancelled := congrArg (fun value : ComplexEuclidean dimension =>
    (cartesianWeight parameters cell point.val)⁻¹ • value) weightedEquality
  simpa only [inv_smul_smul₀ (cartesianWeight_pos parameters cell point.val).ne'] using cancelled

end Grad.CartesianCoreRecovery
