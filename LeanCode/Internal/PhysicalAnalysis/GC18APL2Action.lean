import GC18APSpace
import MK1Construction

noncomputable section

open MeasureTheory

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.MatrixMultiplier

theorem closedOperator_continuousOn {input output : ℕ}
    (coefficient : C(ClosedDisk, OperatorValue input output)) :
    ContinuousOn (closedDiskLift coefficient) openUnitDisk := by
  rw [continuousOn_iff_continuous_domRestrict]
  have equality : openUnitDisk.domRestrict (closedDiskLift coefficient) =
      fun point : OpenDisk => coefficient (openDiskInclusion point) := by
    funext point
    simp [Set.domRestrict, closedDiskLift, openDiskInclusion,
      openDiskMembershipClosed point.val point.property]
  rw [equality]
  exact coefficient.continuous.comp (continuous_subtype_val.subtype_mk _)

theorem closedOperator_measurable {input output : ℕ}
    (coefficient : C(ClosedDisk, OperatorValue input output)) :
    AEStronglyMeasurable (closedDiskLift coefficient) (volume.restrict openUnitDisk) :=
  ((closedOperator_continuousOn coefficient).aemeasurable openUnitDisk_isOpen.measurableSet).aestronglyMeasurable

theorem closedOperator_bound {input output : ℕ}
    (coefficient : C(ClosedDisk, OperatorValue input output)) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ‖closedDiskLift coefficient point‖ ≤ ‖coefficient‖ := by
  filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point inside
  simpa only [closedDiskLift, openDiskMembershipClosed point inside, dite_true] using
    ContinuousMap.norm_coe_le_norm coefficient ⟨point, openDiskMembershipClosed point inside⟩

def closedOperatorL2 {input output : ℕ}
    (coefficient : C(ClosedDisk, OperatorValue input output)) : DiskL2 input →L[ℂ] DiskL2 output :=
  matrixMultiplier (volume.restrict openUnitDisk) (closedDiskLift coefficient) ‖coefficient‖
    (closedOperator_measurable coefficient) (closedOperator_bound coefficient)

theorem closedOperatorL2_ae {input output : ℕ}
    (coefficient : C(ClosedDisk, OperatorValue input output)) (field : DiskL2 input) :
    ∀ᵐ point ∂volume.restrict openUnitDisk,
      closedOperatorL2 coefficient field point = closedDiskLift coefficient point (field point) :=
  matrixMultiplier_apply_ae _ _ _ _ _ field

theorem closedOperatorL2_norm_le {input output : ℕ}
    (coefficient : C(ClosedDisk, OperatorValue input output)) : ‖closedOperatorL2 coefficient‖ ≤ ‖coefficient‖ :=
  norm_matrixMultiplier_le _ _ _ _ _ (norm_nonneg coefficient)

theorem closedOperatorL2_apply_norm_le {input output : ℕ}
    (coefficient : C(ClosedDisk, OperatorValue input output)) (field : DiskL2 input) :
    ‖closedOperatorL2 coefficient field‖ ≤ ‖coefficient‖ * ‖field‖ :=
  norm_matrixMultiplier_apply_le _ _ _ _ _ field

theorem closedOperatorL2_closed {input output : ℕ}
    (coefficient : C(ClosedDisk, OperatorValue input output)) (field : C(ClosedDisk, ComplexEuclidean input)) :
    closedOperatorL2 coefficient (closedContinuousToDiskL2 field) =
      closedContinuousToDiskL2 ⟨fun point => coefficient point (field point), coefficient.continuous.clm_apply field.continuous⟩ := by
  apply Lp.ext
  filter_upwards [closedOperatorL2_ae coefficient (closedContinuousToDiskL2 field),
    closedContinuousToDiskL2_ae field,
    closedContinuousToDiskL2_ae ⟨fun point => coefficient point (field point), coefficient.continuous.clm_apply field.continuous⟩,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point action inputValue outputValue inside
  rw [action, inputValue, outputValue]
  simp only [closedDiskLift, openDiskMembershipClosed point inside, dite_true, ContinuousMap.coe_mk]

theorem closedOperatorL2_add {input output : ℕ}
    (first second : C(ClosedDisk, OperatorValue input output)) :
    closedOperatorL2 (first + second) = closedOperatorL2 first + closedOperatorL2 second := by
  apply ContinuousLinearMap.ext
  intro field
  apply Lp.ext
  filter_upwards [closedOperatorL2_ae (first + second) field, closedOperatorL2_ae first field,
    closedOperatorL2_ae second field, Lp.coeFn_add (closedOperatorL2 first field) (closedOperatorL2 second field),
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point total firstValue secondValue addition inside
  change _ = (closedOperatorL2 first field + closedOperatorL2 second field) point
  rw [total, addition, Pi.add_apply, firstValue, secondValue]
  simp only [closedDiskLift, openDiskMembershipClosed point inside, dite_true, ContinuousMap.add_apply,
    add_apply]

theorem closedOperatorL2_smul {input output : ℕ} (scalar : ℂ)
    (coefficient : C(ClosedDisk, OperatorValue input output)) :
    closedOperatorL2 (scalar • coefficient) = scalar • closedOperatorL2 coefficient := by
  apply ContinuousLinearMap.ext
  intro field
  apply Lp.ext
  filter_upwards [closedOperatorL2_ae (scalar • coefficient) field, closedOperatorL2_ae coefficient field,
    Lp.coeFn_smul scalar (closedOperatorL2 coefficient field),
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point total original scaled inside
  change _ = (scalar • closedOperatorL2 coefficient field) point
  rw [total, scaled, Pi.smul_apply, original]
  simp only [closedDiskLift, openDiskMembershipClosed point inside, dite_true, ContinuousMap.smul_apply,
    smul_apply]

/-- The actual coefficient-to-L2 multiplier, bounded bilinearly with
constant one. The inherited DiskL2 norm is the original area norm. -/
def closedOperatorAction (input output : ℕ) :
    C(ClosedDisk, OperatorValue input output) →L[ℂ] DiskL2 input →L[ℂ] DiskL2 output := by
  let mapping : C(ClosedDisk, OperatorValue input output) →ₗ[ℂ] DiskL2 input →L[ℂ] DiskL2 output :=
    { toFun := closedOperatorL2
      map_add' := closedOperatorL2_add
      map_smul' := closedOperatorL2_smul }
  have bounded : ∀ coefficient, ‖mapping coefficient‖ ≤ 1 * ‖coefficient‖ := fun coefficient => by
    change ‖closedOperatorL2 coefficient‖ ≤ 1 * ‖coefficient‖
    simpa only [one_mul] using closedOperatorL2_norm_le coefficient
  exact @LinearMap.mkContinuous ℂ ℂ (C(ClosedDisk, OperatorValue input output))
    (DiskL2 input →L[ℂ] DiskL2 output) _ _ _ _ _ _ (RingHom.id ℂ) mapping 1 bounded

end Grad.GaugeCoefficients.Physical.RadialLedger
