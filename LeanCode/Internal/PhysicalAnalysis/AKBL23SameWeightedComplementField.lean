import AKBL22PuncturedComplementFourier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.AnalyticWeights.Calculus

/-- The actual full-cell C0 kernel is precisely the original radial phase
conjugation of physical C0 applied before the axial Fourier coefficient.
The SAME field is only punctured continuous and L2; no H1 is presupposed. -/
theorem startupComplement_originalField_ae (sigma gamma ell : ℝ)
    (field : StartupL2 3) (raw : ℝ × Spatial → PhysicalValue 3)
    (continuousRaw : ContinuousOn raw {pair | pair.2 ∈ openUnitDisk \ {(0 : Spatial)}})
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      field point cell = physicalWeight sigma gamma ell cell point • angularCoefficient (fun angle => raw (angle,point)) cell) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      originalComplementKernel field point cell = closedFieldExtension (fun closed : ClosedDisk =>
        physicalWeight sigma gamma ell cell closed.val • angularCoefficient
          (fun angle => cartesianComplementValue (fun other : ClosedDisk => raw (angle,other.val)) closed) cell) point := by
  apply ae_all_iff.mpr
  intro cell
  let rawCell : ClosedDisk → PhysicalValue 3 := fun closed => physicalWeight sigma gamma ell cell closed.val •
    angularCoefficient (fun angle => raw (angle,closed.val)) cell
  have cellSame : (fun point => field point cell) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension rawCell := by
    filter_upwards [same,ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point original inside
    let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
    exact (original cell).trans (closedFieldExtension_value rawCell closed).symm
  have complementSame := startupComplement_roughClosedRepresentative field cell rawCell cellSame
  have away : ∀ᵐ point ∂volume.restrict openUnitDisk, point ≠ (0 : Spatial) := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    simp
  filter_upwards [complementSame,away,ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point original nonzero inside
  let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
  have inputAt := closedFieldExtension_value (cartesianComplementValue rawCell) closed
  have outputAt := closedFieldExtension_value (fun closed : ClosedDisk => physicalWeight sigma gamma ell cell closed.val •
    angularCoefficient (fun angle => cartesianComplementValue (fun other : ClosedDisk => raw (angle,other.val)) closed) cell) closed
  rw [original,inputAt,outputAt]
  change cartesianComplementValue (fun other : ClosedDisk => physicalWeight sigma gamma ell cell other.val •
    angularCoefficient (fun angle => raw (angle,other.val)) cell) closed = _
  rw [startupComplement_originalWeight,startupComplement_punctured_axialCoefficient raw continuousRaw cell closed
    (norm_pos_iff.mpr nonzero) inside]

end Grad.CartesianStartup
