import AKBL25SamePhysicalMatrixContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.BoundaryTrace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnalyticWeights.Calculus

 def StartupWeightedRep {dimension : ℕ} (sigma gamma ell : ℝ)
    (field : StartupL2 dimension) (raw : ℝ × Spatial → PhysicalValue dimension) : Prop :=
  ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
    field point cell = physicalWeight sigma gamma ell cell point • angularCoefficient (fun angle => raw (angle,point)) cell

 theorem startupDisk_ae_nonzero : ∀ᵐ point ∂volume.restrict openUnitDisk, point ≠ (0 : Spatial) := by
  apply ae_restrict_of_ae
  rw [ae_iff]
  simp

 theorem StartupOrbitContinuous.axial_ae {dimension : ℕ} {raw : ℝ × Spatial → PhysicalValue dimension}
    (regular : StartupOrbitContinuous raw) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, Continuous (fun angle => raw (angle,point)) := by
  filter_upwards [startupDisk_ae_nonzero,ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point nonzero inside
  exact regular.axial ⟨point,openDiskMembershipClosed point inside⟩ (norm_pos_iff.mpr nonzero) inside

 theorem StartupWeightedRep.matrix {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    {field : StartupL2 input} {raw : ℝ × Spatial → PhysicalValue input}
    (same : StartupWeightedRep sigma gamma ell field raw) (regular : StartupOrbitContinuous raw) :
    StartupWeightedRep sigma gamma ell (originalMatrixKernel admissible family coherent field) (startupRawMatrix family raw) :=
  startupMatrix_originalField_ae admissible family coherent field (fun point angle => raw (angle,point)) regular.axial_ae same

 theorem StartupWeightedRep.complement {sigma gamma ell : ℝ}
    {field : StartupL2 3} {raw : ℝ × Spatial → PhysicalValue 3}
    (same : StartupWeightedRep sigma gamma ell field raw) (regular : StartupOrbitContinuous raw) :
    StartupWeightedRep sigma gamma ell (originalComplementKernel field) (startupRawComplement raw) := by
  apply ae_all_iff.mpr
  intro cell
  let rawCell : ClosedDisk → PhysicalValue 3 := fun closed => physicalWeight sigma gamma ell cell closed.val •
    angularCoefficient (fun angle => raw (angle,closed.val)) cell
  have cellSame : (fun point => field point cell) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension rawCell := by
    filter_upwards [same,ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point original inside
    let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
    exact (original cell).trans (closedFieldExtension_value rawCell closed).symm
  have complementSame := startupComplement_roughClosedRepresentative field cell rawCell cellSame
  filter_upwards [complementSame,startupDisk_ae_nonzero,ae_restrict_mem openUnitDisk_isOpen.measurableSet]
    with point original nonzero inside
  let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
  have inputAt := closedFieldExtension_value (cartesianComplementValue rawCell) closed
  rw [original,inputAt]
  change cartesianComplementValue (fun other : ClosedDisk => physicalWeight sigma gamma ell cell other.val •
    angularCoefficient (fun angle => raw (angle,other.val)) cell) closed = _
  rw [startupComplement_originalWeight,regular.complement_fourier cell closed (norm_pos_iff.mpr nonzero) inside]

 theorem StartupWeightedRep.ext {dimension : ℕ} {sigma gamma ell : ℝ}
    {first second : StartupL2 dimension} {raw : ℝ × Spatial → PhysicalValue dimension}
    (firstSame : StartupWeightedRep sigma gamma ell first raw)
    (secondSame : StartupWeightedRep sigma gamma ell second raw) : first = second := by
  apply startupField_ae_ext
  filter_upwards [firstSame,secondSame] with point firstAt secondAt
  intro cell
  exact (firstAt cell).trans (secondAt cell).symm

 theorem StartupWeightedRep.congr_raw {dimension : ℕ} {sigma gamma ell : ℝ}
    {field : StartupL2 dimension} {first second : ℝ × Spatial → PhysicalValue dimension}
    (same : StartupWeightedRep sigma gamma ell field first)
    (equal : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ angle, first (angle,point) = second (angle,point)) :
    StartupWeightedRep sigma gamma ell field second := by
  filter_upwards [same,equal] with point original equalAt
  intro cell
  rw [original cell]
  exact congrArg (fun function : ℝ → PhysicalValue dimension =>
    physicalWeight sigma gamma ell cell point • angularCoefficient function cell) (funext equalAt)

end Grad.CartesianStartup
