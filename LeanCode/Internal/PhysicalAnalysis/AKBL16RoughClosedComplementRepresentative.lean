import AKBL15RoughClosedCharacterRepresentative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.Constraints Grad.Constraints.Gauges Grad.PhysicalFamily Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Algebra

 theorem startupClosedRepresentative_add {dimension : ℕ}
    (first second : StartupL2 dimension) (cell : ℤ)
    (rawFirst rawSecond : ClosedDisk → PhysicalValue dimension)
    (firstSame : (fun point => first point cell) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension rawFirst)
    (secondSame : (fun point => second point cell) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension rawSecond) :
    (fun point => (first+second) point cell) =ᵐ[volume.restrict openUnitDisk]
      closedFieldExtension (fun point => rawFirst point+rawSecond point) := by
  filter_upwards [Lp.coeFn_add first second,firstSame,secondSame,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point addition firstAt secondAt inside
  let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
  rw [addition]
  change first point cell+second point cell = _
  rw [firstAt,secondAt]
  exact (congrArg₂ (fun first second : PhysicalValue dimension => first+second)
    (closedFieldExtension_value rawFirst closed) (closedFieldExtension_value rawSecond closed)).trans
      (closedFieldExtension_value (fun point => rawFirst point+rawSecond point) closed).symm

 theorem startupClosedRepresentative_sub {dimension : ℕ}
    (first second : StartupL2 dimension) (cell : ℤ)
    (rawFirst rawSecond : ClosedDisk → PhysicalValue dimension)
    (firstSame : (fun point => first point cell) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension rawFirst)
    (secondSame : (fun point => second point cell) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension rawSecond) :
    (fun point => (first-second) point cell) =ᵐ[volume.restrict openUnitDisk]
      closedFieldExtension (fun point => rawFirst point-rawSecond point) := by
  filter_upwards [Lp.coeFn_sub first second,firstSame,secondSame,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point addition firstAt secondAt inside
  let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
  rw [addition]
  change first point cell-second point cell = _
  rw [firstAt,secondAt]
  exact (congrArg₂ (fun first second : PhysicalValue dimension => first-second)
    (closedFieldExtension_value rawFirst closed) (closedFieldExtension_value rawSecond closed)).trans
      (closedFieldExtension_value (fun point => rawFirst point-rawSecond point) closed).symm

 theorem startupClosedRepresentative_smul {dimension : ℕ} (scalar : ℂ)
    (field : StartupL2 dimension) (cell : ℤ) (raw : ClosedDisk → PhysicalValue dimension)
    (same : (fun point => field point cell) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension raw) :
    (fun point => (scalar • field) point cell) =ᵐ[volume.restrict openUnitDisk]
      closedFieldExtension (fun point => scalar • raw point) := by
  filter_upwards [Lp.coeFn_smul scalar field,same,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point scaling original inside
  let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
  rw [scaling]
  change scalar • field point cell = _
  rw [original]
  exact (congrArg (fun value : PhysicalValue dimension => scalar • value)
    (closedFieldExtension_value raw closed)).trans
      (closedFieldExtension_value (fun point => scalar • raw point) closed).symm

 theorem startupPoint_closedRepresentative {input output : ℕ} (mapping : OperatorValue input output)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : StartupL2 input) (cell : ℤ)
    (raw : ClosedDisk → PhysicalValue input)
    (same : (fun point => field point cell) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension raw) :
    (fun point => startupPointKernel mapping orthogonal field point cell) =ᵐ[volume.restrict openUnitDisk]
      closedFieldExtension (fun closed => mapping (raw (orthogonalClosedPoint orthogonal closed))) := by
  have moved := (startupOrthogonal_disk_preserving orthogonal).quasiMeasurePreserving.ae same
  filter_upwards [startupPointKernel_field_ae mapping orthogonal field,moved,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point value original inside
  let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
  rw [value cell,original]
  exact (congrArg mapping (closedFieldExtension_value raw (orthogonalClosedPoint orthogonal closed))).trans
    (closedFieldExtension_value (fun closed => mapping (raw (orthogonalClosedPoint orthogonal closed))) closed).symm

 theorem startupAverage_roughClosedRepresentative (field : StartupL2 2) (cell : ℤ)
    (raw : ClosedDisk → PhysicalValue 2)
    (same : (fun point => field point cell) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension raw) :
    (fun point => originalAverageKernel field point cell) =ᵐ[volume.restrict openUnitDisk]
      closedFieldExtension (closedEquivariantValue raw) := by
  exact startupClosedRepresentative_add _ _ cell _ _
    (startupValue_closedRepresentative positiveHelicity _ cell _ (startupCharacter_closedRepresentative 1 field cell raw same))
    (startupValue_closedRepresentative negativeHelicity _ cell _ (startupCharacter_closedRepresentative (-1) field cell raw same))

 theorem startupTangential_roughClosedRepresentative (field : StartupL2 2) (cell : ℤ)
    (raw : ClosedDisk → PhysicalValue 2)
    (same : (fun point => field point cell) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension raw) :
    (fun point => originalTangentialKernel field point cell) =ᵐ[volume.restrict openUnitDisk]
      closedFieldExtension (closedTangentialValue raw) := by
  have average := startupAverage_roughClosedRepresentative field cell raw same
  exact startupClosedRepresentative_smul (1/2 : ℂ) _ cell _
    (startupClosedRepresentative_sub _ _ cell _ _ average
      (startupPoint_closedRepresentative reflectionValueMap cartesianReflectionEquiv _ cell _ average))

/-- The actual fixed complement on SAME rough full-cell fields has the
literal Cartesian C0 value, without continuity or H1 at the axis. -/
 theorem startupComplement_roughClosedRepresentative (field : StartupL2 3) (cell : ℤ)
    (raw : ClosedDisk → PhysicalValue 3)
    (same : (fun point => field point cell) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension raw) :
    (fun point => originalComplementKernel field point cell) =ᵐ[volume.restrict openUnitDisk]
      closedFieldExtension (cartesianComplementValue raw) := by
  exact startupClosedRepresentative_add _ _ cell _ _
    (startupValue_closedRepresentative planarInclusionMap _ cell _
      (startupTangential_roughClosedRepresentative _ cell _ (startupValue_closedRepresentative planarPartMap field cell raw same)))
    (startupValue_closedRepresentative toroidalInclusionMap _ cell _
      (startupCharacter_closedRepresentative 0 _ cell _ (startupValue_closedRepresentative toroidalPartMap field cell raw same)))

 theorem startupCircle_roughClosedRepresentative (field : StartupL2 3) (cell : ℤ)
    (raw : ClosedDisk → PhysicalValue 3)
    (same : (fun point => field point cell) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension raw) :
    (fun point => originalCircleKernel field point cell) =ᵐ[volume.restrict openUnitDisk]
      closedFieldExtension (fun point => raw point-cartesianComplementValue raw point) :=
  startupClosedRepresentative_sub _ _ cell _ _ same (startupComplement_roughClosedRepresentative field cell raw same)

end Grad.CartesianStartup
