import AKCA7NativeFourierPointwiseBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.ActualPuncturedFamily Grad.AnnularRestriction Grad.ActualCartesianDescent
open Grad.ActualNativeCellMoments
open Grad.CartesianCoreRecovery Grad.SourceCollarFullSource

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)
include compatible

 theorem nativeFamilyFull_fourth_bound (point : SpatialPlane × ℝ)
    (inside : ‖point.1‖ ∈ Ioc (0 : ℝ) 1) :
    ‖gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves point‖ ≤
      nativeFieldReadoutConstant parameters dimension *
        ‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves 4 ‖point.1‖‖ := by
  let index := selectedInnerCollar lower cofinal ‖point.1‖ inside.1
  have collar : ‖point.1‖ ∈ Icc (lower index) 1 :=
    ⟨(selectedInnerCollar_lt lower cofinal ‖point.1‖ inside.1).le,inside.2⟩
  rw [gluedCartesianFamilyField_same parameters lower positive bounded cofinal decreasing rows curves compatible index point collar,
    gluedWeightedFamilyCurve_same parameters lower positive bounded cofinal decreasing rows curves compatible 4 index ‖point.1‖ collar]
  simp only [SmoothLowPhysicalRow.cartesianField,cartesianPhysicalField,cartesianFromPolar,Grad.BoundaryLift.complexCoordinate_norm]
  exact nativeFullField_fourth_bound (curves index) (bounded index) ‖point.1‖ collar _

 theorem recoveredCoreCell_fourth_bound (core : ACore parameters dimension)
    (same : ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle)) =
        gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (point.val,axial))
    (point : ClosedDisk) (nonzero : 0 < ‖point.val‖) (cell : ℤ) :
    ‖(core.val cell).value point‖ ≤ nativeFieldReadoutConstant parameters dimension *
      ‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves 4 ‖point.val‖‖ := by
  rw [← originalPhysicalClosedJet_angularCell parameters core point cell]
  apply angularCoefficient_norm_le
  · exact (originalPhysicalClosedJet parameters core).value.continuous.comp
      (continuous_const.prodMk (show Continuous (fun axial : ℝ => (axial : CellCircle)) from QuotientAddGroup.continuous_mk))
  · exact mul_nonneg (nativeFieldReadoutConstant_nonnegative parameters dimension) (norm_nonneg _)
  · intro axial _
    rw [same point nonzero axial]
    exact nativeFamilyFull_fourth_bound parameters lower positive bounded cofinal decreasing rows curves compatible
      (point.val,axial) ⟨nonzero,point.property⟩

end Grad.OriginalCoreRealization
