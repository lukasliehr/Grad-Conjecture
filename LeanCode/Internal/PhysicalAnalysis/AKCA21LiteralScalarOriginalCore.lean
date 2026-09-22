import AKCA20SameScalarRadiusFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.CartesianStartup
open Grad.WeightedJets Grad.BoundaryTrace Grad.SourceCollarDivision Grad.ActualSmoothPhysicalField
open Grad.ActualCartesianDescent Grad.ActualPuncturedFamily Grad.AnnularRestriction Grad.SpatialDilation
open Grad.CartesianCoreRecovery Grad.AnnularCurrentSource

/-- Genuine all-order graphs of literal S recover its original analytic
core directly. The auxiliary S/r is only a punctured native row. -/
theorem originalScalarLocalizedAllOrder_physicalCore
    (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow 1 (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction 1 (lower second) (lower first) (decreasing ordered) (rows second)=rows first)
    (scale : Scale) (near : ℝ) (nearPositive : 0 < near) (nearOne : near ≤ 1)
    (field : StartupL2 1) (jets : ∀ grade, GraphGrade 1 grade grade openUnitDisk)
    (sameBase : ∀ grade, base 1 grade openUnitDisk (fun _ => grade) (jets grade) = field)
    (cutoff : SpatialPlane → ℝ) (cutoffOne : ∀ point, ‖point‖ < near → cutoff point = 1)
    (sameRaw : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      field point cell = cutoff point •
        (Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma scale.val cell point •
          (‖scale.val • point‖ • gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell (scale.val • point)))) :
    ∃ core : ACore parameters 1,∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle)) =
        ‖point.val‖ • gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (point.val,axial) := by
  obtain ⟨core,_,same⟩ := originalWidthLocalizedAllOrder_physicalCore parameters lower positive bounded cofinal decreasing
    (fun index => radialRadiusRow (lower index) (positive index) (rows index))
    (fun index => scalarRadiusCurves (curves index))
    (scalarRadiusFamily_compatible lower positive decreasing rows compatible) scale near nearPositive nearOne field jets sameBase cutoff cutoffOne
    (by
      filter_upwards [sameRaw,startupDisk_ae_nonzero,ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point actual nonzero inside
      have scaledNonzero : scale.val • point≠0 := smul_ne_zero scale.property.1.ne' nonzero
      have scaledInside : ‖scale.val • point‖<1 := by
        rw [norm_smul,Real.norm_of_nonneg scale.property.1.le]
        exact (mul_le_of_le_one_left (norm_nonneg point) scale.property.2).trans_lt inside
      intro cell
      rw [scalarRadiusFamily_cell parameters lower positive bounded cofinal decreasing rows curves compatible
        (scale.val • point) scaledNonzero scaledInside cell]
      exact actual cell)
  refine ⟨core,fun point nonzero axial => ?_⟩
  exact (same point nonzero axial).trans (scalarRadiusFamily_fullField parameters lower positive bounded cofinal decreasing rows curves compatible
    (point.val,axial) ⟨nonzero,point.property⟩)

end Grad.OriginalCoreRealization
