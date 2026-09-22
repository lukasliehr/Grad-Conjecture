import AKBL30PuncturedFixedGaugeMeans

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.BoundaryTrace
open Grad.Constraints Grad.Constraints.Gauges Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.AnalyticWeights.Calculus

/-- The two literal native physical gauge means imply the actual rough C0
kernel is zero on the SAME weighted full-cell field. This is the exact
Cartesian gauge input needed by the current recovery theorem. -/
theorem startupSameWeighted_gauge_zero (sigma gamma ell : ℝ)
    (field : StartupL2 3) (raw : ℤ → Spatial → PhysicalValue 3)
    (continuousRaw : ∀ cell, ContinuousOn (raw cell) (openUnitDisk \ {(0 : Spatial)}))
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      field point cell = physicalWeight sigma gamma ell cell point • raw cell point)
    (gauges : ∀ (radius : ℝ) (_positive : 0 < radius) (_inside : radius < 1) (bounded : |radius| ≤ 1) (cell : ℤ),
      angularCoefficient (fun polar => polarTangentialComponent polar
        (planarPartMap (raw cell (Grad.Constraints.polarClosedPoint radius bounded polar).val))) 0 = 0 ∧
      angularCoefficient (fun polar => toroidalPartMap
        (raw cell (Grad.Constraints.polarClosedPoint radius bounded polar).val)) 0 = 0) :
    originalComplementKernel field = 0 := by
  apply startupField_ae_ext
  apply ae_all_iff.mpr
  intro cell
  let rawCell : ClosedDisk → PhysicalValue 3 := fun closed => physicalWeight sigma gamma ell cell closed.val • raw cell closed.val
  have cellSame : (fun point => field point cell) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension rawCell := by
    filter_upwards [same,ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point original inside
    let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
    exact (original cell).trans (closedFieldExtension_value rawCell closed).symm
  have complementSame := startupComplement_roughClosedRepresentative field cell rawCell cellSame
  filter_upwards [complementSame,startupDisk_ae_nonzero,ae_restrict_mem openUnitDisk_isOpen.measurableSet,
    Lp.coeFn_zero (CellValues 3) 2 (volume.restrict openUnitDisk)] with point original nonzero inside zero
  let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
  have inputAt := closedFieldExtension_value (cartesianComplementValue rawCell) closed
  have positive : 0 < ‖point‖ := norm_pos_iff.mpr nonzero
  have bounded : |‖point‖| ≤ 1 := by rw [abs_of_nonneg (norm_nonneg _)]; exact inside.le
  obtain ⟨angle,polar⟩ := startupClosedPoint_polar closed
  have mean := gauges ‖point‖ positive inside bounded cell
  have projected := startupPuncturedComplement_zero_of_gaugeMeans (raw cell) (continuousRaw cell)
    ‖point‖ positive inside bounded angle mean.1 mean.2
  have atPoint : cartesianComplementValue (fun other : ClosedDisk => raw cell other.val) closed = 0 := by
    rw [polar] at projected
    exact projected
  rw [original,inputAt,zero]
  change cartesianComplementValue (fun other : ClosedDisk => physicalWeight sigma gamma ell cell other.val • raw cell other.val) closed = 0
  rw [startupComplement_originalWeight,atPoint,smul_zero]

end Grad.CartesianStartup
