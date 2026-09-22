import AKBV18SameCompatibleNativeOriginalCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.CartesianStartup
open Grad.WeightedJets Grad.BoundaryTrace Grad.SourceCollarDivision Grad.ActualSmoothPhysicalField
open Grad.ActualCartesianDescent Grad.ActualPuncturedFamily Grad.AnnularRestriction Grad.DiskExtension.Operator Grad.Constraints

theorem originalPhysicalClosedJet_angularCell {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (point : ClosedDisk) (cell : ℤ) :
    angularCoefficient (fun axial => (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle))) cell =
      (core.val cell).value point := by
  calc
    _ = fourierCoeff (fun circle => (originalPhysicalClosedJet parameters core).value (point,circle)) cell :=
      angularCoefficient_circle _ cell
    _ = diskCellFourierValue (originalPhysicalClosedJet parameters core).value cell point :=
      (diskCellFourierValue_apply _ cell point).symm
    _ = _ := by
      change (diskCellFourierCoefficientJet (originalPhysicalClosedJet parameters core) cell).value point = _
      rw [originalPhysicalClosedJet_fourierCoefficient]

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)

include compatible in
theorem originalCore_sameNativePhysicalValue (core : ACore parameters dimension)
    (sameCells : ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ cell : ℤ,
      (core.val cell).value point = gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point.val)
    (point : ClosedDisk) (nonzero : 0 < ‖point.val‖) (axial : ℝ) :
    (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle)) =
      gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (point.val,axial) := by
  let index := selectedInnerCollar lower cofinal ‖point.val‖ nonzero
  have inside : ‖point.val‖ ∈ Icc (lower index) 1 :=
    ⟨(selectedInnerCollar_lt lower cofinal ‖point.val‖ nonzero).le,point.property⟩
  have nativeFull : (fun current => gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (point.val,current)) =
      fun current => (curves index).cartesianField (bounded index) (point.val,current) :=
    funext (fun current => gluedCartesianFamilyField_same parameters lower positive bounded cofinal decreasing rows curves compatible index (point.val,current) inside)
  have nativeContinuous : Continuous (fun current => gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (point.val,current)) := by
    rw [nativeFull]
    simp only [SmoothLowPhysicalRow.cartesianField,cartesianPhysicalField,cartesianFromPolar,Grad.BoundaryLift.complexCoordinate_norm]
    exact ((curves index).fullField_continuous_angles (bounded index) ‖point.val‖ inside).comp
      (continuous_const.prodMk continuous_id)
  have nativePeriodic : Function.Periodic
      (fun current => gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (point.val,current)) (2*Real.pi) := by
    rw [nativeFull]
    intro current
    exact (curves index).fullField_cell_periodic (bounded index) _ _ current
  have originalContinuous : Continuous
      (fun current : ℝ => (originalPhysicalClosedJet parameters core).value (point,(current : CellCircle))) :=
    (originalPhysicalClosedJet parameters core).value.continuous.comp
      (continuous_const.prodMk (show Continuous (fun current : ℝ => (current : CellCircle)) from QuotientAddGroup.continuous_mk))
  have originalPeriodic : Function.Periodic
      (fun current : ℝ => (originalPhysicalClosedJet parameters core).value (point,(current : CellCircle))) (2*Real.pi) := by
    intro current
    change (originalPhysicalClosedJet parameters core).value (point,((current + 2*Real.pi : ℝ) : CellCircle)) =
      (originalPhysicalClosedJet parameters core).value (point,(current : CellCircle))
    rw [AddCircle.coe_add_period]
  apply congrFun (periodicFourier_ext _ _ originalContinuous nativeContinuous originalPeriodic nativePeriodic ?_) axial
  intro cell
  rw [originalPhysicalClosedJet_angularCell,sameCells point nonzero,nativeFull]
  exact compatibleNativeCell_collar parameters lower positive bounded cofinal decreasing rows curves compatible index point.val inside cell

include compatible in
/-- The actual full periodic physical reconstruction, not only its L2 equivalence class, is unchanged by recovering the original analytic core. -/
theorem compatibleLocalizedAllOrder_physicalCore
    (scale upper : ℝ) (scalePositive : 0 < scale) (upperPositive : 0 < upper)
    (upperScale : upper ≤ scale) (upperOne : upper ≤ 1)
    (field : StartupL2 dimension) (jets : ∀ grade, GraphGrade dimension grade grade openUnitDisk)
    (sameBase : ∀ grade, base dimension grade openUnitDisk (fun _ => grade) (jets grade) = field)
    (cutoff : SpatialPlane → ℝ) (cutoffOne : ∀ point, scale * ‖point‖ < upper → cutoff point = 1)
    (sameRaw : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      field point cell = cutoff point • (cartesianWeight parameters cell (scale • point) •
        gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell (scale • point))) :
    ∃ core : ACore parameters dimension,
      (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ cell : ℤ,
        (core.val cell).value point = gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point.val) ∧
      ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
        (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle)) =
          gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (point.val,axial) := by
  obtain ⟨core,same⟩ := compatibleLocalizedAllOrder_originalCore parameters lower positive bounded cofinal decreasing rows curves compatible
    scale upper scalePositive upperPositive upperScale upperOne field jets sameBase cutoff cutoffOne sameRaw
  exact ⟨core,same,originalCore_sameNativePhysicalValue parameters lower positive bounded cofinal decreasing rows curves compatible core same⟩

end Grad.CartesianCoreRecovery
