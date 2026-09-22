import AKDB5GenuineScalarOriginalCore
import AKDB6SameNativeAllOrderRecovery
import AKCA21LiteralScalarOriginalCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.CartesianStartup
open Grad.WeightedJets Grad.BoundaryTrace Grad.SourceCollarDivision Grad.ActualSmoothPhysicalField
open Grad.ActualCartesianDescent Grad.ActualPuncturedFamily Grad.AnnularRestriction Grad.SpatialDilation
open Grad.CartesianCoreRecovery Grad.AnalyticWeights.Calculus

/-- Whole-disk native graphs directly recover the SAME original core,
with no additional localization and no loss of analytic width. -/
theorem originalNativeAllOrder_physicalCore {dimension : ℕ}
    (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)
    (scale : Scale) (field : StartupL2 dimension)
    (regular : ∀ grade, ∃ graph : GraphGrade dimension grade grade openUnitDisk,
      base dimension grade openUnitDisk (fun _ => grade) graph=field)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      field point cell=physicalWeight parameters.sigma0 parameters.gamma scale.val cell point •
        gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell (scale.val • point)) :
    ∃ core : ACore parameters dimension,
      (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ cell : ℤ,
        (core.val cell).value point=gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point.val) ∧
      ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
        (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle))=
          gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (point.val,axial) := by
  apply originalWidthLocalizedAllOrder_physicalCore parameters lower positive bounded cofinal decreasing rows curves compatible
    scale 1 zero_lt_one le_rfl field (fun grade => (regular grade).choose) (fun grade => (regular grade).choose_spec)
    (fun _ => 1) (fun _ _ => rfl)
  simpa only [one_smul] using same

/-- The scalar fixed by the weak force is Xi(ell Y)/ell. Its genuine
all-order graphs, after multiplication by ell, recover the original Xi
core from the SAME punctured Xi/r family. -/
theorem originalNativePsiAllOrder_xiCore
    (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow 1 (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction 1 (lower second) (lower first) (decreasing ordered) (rows second)=rows first)
    (scale : Scale) (psi : StartupL2 1)
    (regular : ∀ grade, ∃ graph : GraphGrade 1 grade grade openUnitDisk,
      base 1 grade openUnitDisk (fun _ => grade) graph=psi)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      psi point cell=physicalWeight parameters.sigma0 parameters.gamma scale.val cell point •
        (‖point‖ • gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell (scale.val • point))) :
    ∃ core : ACore parameters 1,∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle))=
        ‖point.val‖ • gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (point.val,axial) := by
  apply originalScalarLocalizedAllOrder_physicalCore parameters lower positive bounded cofinal decreasing rows curves compatible
    scale 1 zero_lt_one le_rfl ((scale.val : ℂ) • psi)
    (fun grade => (scale.val : ℂ) • (regular grade).choose)
    (fun grade => by rw [map_smul,(regular grade).choose_spec]) (fun _ => 1) (fun _ _ => rfl)
  filter_upwards [same,Lp.coeFn_smul (scale.val : ℂ) psi] with point actual scaled
  intro cell
  rw [scaled,Pi.smul_apply,lp.coeFn_smul,Pi.smul_apply,actual cell,one_smul]
  rw [Complex.coe_smul,smul_comm scale.val,smul_smul,norm_smul,Real.norm_of_nonneg scale.property.1.le]
  simp only [smul_smul,mul_assoc]

end Grad.OriginalCoreRealization
