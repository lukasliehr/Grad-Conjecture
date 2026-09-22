import AXI1FaithfulL2
import MK1Construction

noncomputable section

open MeasureTheory
open scoped Topology

namespace Grad.RawSourceFaithfulness

open Grad.ClosedJets Grad.CartesianState Grad.MatrixMultiplier

variable {dimension : ℕ}

def scalarCoefficient (factor : SpatialPlane → ℂ) (point : SpatialPlane) :
    ComplexEuclidean dimension →L[ℂ] ComplexEuclidean dimension :=
  factor point • ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)

theorem scalarCoefficient_measurable (factor : SpatialPlane → ℂ) (smooth : Continuous factor) :
    AEStronglyMeasurable (scalarCoefficient (dimension := dimension) factor)
      (volume.restrict openUnitDisk) :=
  (smooth.smul continuous_const).aestronglyMeasurable

theorem scalarCoefficient_bound (factor : SpatialPlane → ℂ) (constant : ℝ)
    (bounded : ∀ point ∈ openUnitDisk, ‖factor point‖ ≤ constant) :
    ∀ᵐ point ∂volume.restrict openUnitDisk,
      ‖scalarCoefficient (dimension := dimension) factor point‖ ≤ constant := by
  filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point member
  calc
    _ = ‖factor point‖ * ‖ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)‖ := norm_smul _ _
    _ ≤ ‖factor point‖ * 1 :=
      mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
    _ ≤ constant := by simpa only [mul_one] using bounded point member

def diskScalarMultiplier (factor : SpatialPlane → ℂ) (smooth : Continuous factor)
    (constant : ℝ) (bounded : ∀ point ∈ openUnitDisk, ‖factor point‖ ≤ constant) :
    DiskL2 dimension →L[ℂ] DiskL2 dimension :=
  matrixMultiplier (volume.restrict openUnitDisk) (scalarCoefficient factor) constant
    (scalarCoefficient_measurable factor smooth) (scalarCoefficient_bound factor constant bounded)

theorem diskScalarMultiplier_ae (factor : SpatialPlane → ℂ) (smooth : Continuous factor)
    (constant : ℝ) (bounded : ∀ point ∈ openUnitDisk, ‖factor point‖ ≤ constant)
    (field : DiskL2 dimension) :
    ∀ᵐ point ∂volume.restrict openUnitDisk,
      diskScalarMultiplier factor smooth constant bounded field point = factor point • field point :=
  matrixMultiplier_apply_ae _ _ _ _ _ field

theorem diskScalarMultiplier_closed (factor : SpatialPlane → ℂ) (smooth : Continuous factor)
    (constant : ℝ) (bounded : ∀ point ∈ openUnitDisk, ‖factor point‖ ≤ constant)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    diskScalarMultiplier factor smooth constant bounded (closedContinuousToDiskL2 field) =
      closedContinuousToDiskL2
        (⟨fun point => factor point.val • field point,
          (smooth.comp continuous_subtype_val).smul field.continuous⟩) := by
  apply Lp.ext
  filter_upwards [diskScalarMultiplier_ae factor smooth constant bounded (closedContinuousToDiskL2 field),
    closedContinuousToDiskL2_ae field,
    closedContinuousToDiskL2_ae
      (⟨fun point => factor point.val • field point,
        (smooth.comp continuous_subtype_val).smul field.continuous⟩),
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point literal first second member
  rw [literal, first, second]
  simp only [closedDiskLift, openDiskMembershipClosed point member, dite_true,
    ContinuousMap.coe_mk]

theorem diskScalarMultiplier_injective (factor : SpatialPlane → ℂ) (smooth : Continuous factor)
    (constant : ℝ) (bounded : ∀ point ∈ openUnitDisk, ‖factor point‖ ≤ constant)
    (nonzero : ∀ᵐ point ∂volume.restrict openUnitDisk, factor point ≠ 0) :
    Function.Injective (diskScalarMultiplier (dimension := dimension) factor smooth constant bounded) := by
  intro first second equality
  apply Lp.ext
  have equalFunctions := Lp.ext_iff.mp equality
  filter_upwards [diskScalarMultiplier_ae factor smooth constant bounded first,
    diskScalarMultiplier_ae factor smooth constant bounded second, equalFunctions, nonzero]
    with point firstLaw secondLaw equality notZero
  rw [firstLaw, secondLaw] at equality
  have cancelled := congrArg
    (fun value : ComplexEuclidean dimension => (factor point)⁻¹ • value) equality
  simpa only [smul_smul, inv_mul_cancel₀ notZero, one_smul] using cancelled

end Grad.RawSourceFaithfulness
