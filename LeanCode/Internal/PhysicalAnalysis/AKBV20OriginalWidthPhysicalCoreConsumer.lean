import AKBV19SameOriginalPhysicalReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.CartesianStartup
open Grad.WeightedJets Grad.BoundaryTrace Grad.SourceCollarDivision Grad.ActualSmoothPhysicalField
open Grad.ActualCartesianDescent Grad.ActualPuncturedFamily Grad.AnnularRestriction Grad.SpatialDilation

/-- Direct consumer of the standard startup output with its literal original physicalWeight at the chosen scale. All cell and full periodic physical values belong to one original ACore, including the outer boundary. -/
theorem originalWidthLocalizedAllOrder_physicalCore {dimension : ℕ}
    (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)
    (scale : Scale) (near : ℝ) (nearPositive : 0 < near) (nearOne : near ≤ 1)
    (field : StartupL2 dimension) (jets : ∀ grade, GraphGrade dimension grade grade openUnitDisk)
    (sameBase : ∀ grade, base dimension grade openUnitDisk (fun _ => grade) (jets grade) = field)
    (cutoff : SpatialPlane → ℝ) (cutoffOne : ∀ point, ‖point‖ < near → cutoff point = 1)
    (sameRaw : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      field point cell = cutoff point •
        (Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma scale.val cell point •
          gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell (scale.val • point))) :
    ∃ core : ACore parameters dimension,
      (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ cell : ℤ,
        (core.val cell).value point = gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point.val) ∧
      ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
        (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle)) =
          gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (point.val,axial) := by
  apply compatibleLocalizedAllOrder_physicalCore parameters lower positive bounded cofinal decreasing rows curves compatible
    scale.val (scale.val*near) scale.property.1 (mul_pos scale.property.1 nearPositive)
    (by nlinarith [scale.property.1]) (by nlinarith [scale.property.1,scale.property.2])
    field jets sameBase cutoff
  · intro point small
    apply cutoffOne point
    nlinarith [scale.property.1]
  · filter_upwards [sameRaw] with point actual
    intro cell
    have phase : cartesianWeight parameters cell (scale.val • point) =
        Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma scale.val cell point :=
      (startupPhysicalWeight_dilation parameters.sigma0 parameters.gamma scale.val scale.property.1.le cell point).symm
    rw [phase]
    exact actual cell

end Grad.CartesianCoreRecovery
