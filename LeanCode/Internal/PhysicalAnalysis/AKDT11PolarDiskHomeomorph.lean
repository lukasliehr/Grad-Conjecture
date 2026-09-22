import AKDT10UnitCircleHomeomorph

noncomputable section
open Set
open scoped Topology

namespace Grad.PhysicalGeometry
open Grad.MainTarget

abbrev PuncturedDisk := {point : ClosedDisk // point.val ≠ 0}
abbrev PolarDiskDomain := Ioc (0 : ℝ) 1 × CellCircle

def normalizedDiskDirection (point : PuncturedDisk) : UnitPlaneCircle :=
  ⟨‖point.val.val‖⁻¹ • point.val.val, by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr point.property⟩

theorem normalizedDiskDirection_continuous : Continuous normalizedDiskDirection := by
  have base : Continuous (fun point : PuncturedDisk => point.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact ((base.norm.inv₀ (fun point => norm_ne_zero_iff.mpr point.property)).smul base).subtype_mk _

def polarDiskValue (argument : PolarDiskDomain) : Plane := argument.1.val • unitDiskCircle argument.2

theorem polarDiskValue_norm (argument : PolarDiskDomain) : ‖polarDiskValue argument‖ = argument.1.val := by
  rw [polarDiskValue, norm_smul, Real.norm_of_nonneg argument.1.property.1.le, unitDiskCircle_norm, mul_one]

def polarDiskPoint (argument : PolarDiskDomain) : PuncturedDisk :=
  ⟨⟨polarDiskValue argument, by rw [polarDiskValue_norm]; exact argument.1.property.2⟩, by
    apply norm_ne_zero_iff.mp
    rw [polarDiskValue_norm]
    exact argument.1.property.1.ne'⟩

theorem polarDiskPoint_continuous : Continuous polarDiskPoint := by
  have base : Continuous polarDiskValue :=
    (continuous_subtype_val.comp continuous_fst).smul (unitDiskCircle_continuous.comp continuous_snd)
  exact (base.subtype_mk _).subtype_mk _

def polarDiskInverse (point : PuncturedDisk) : PolarDiskDomain :=
  (⟨‖point.val.val‖, norm_pos_iff.mpr point.property, point.val.property⟩,
    unitPlaneAngle (normalizedDiskDirection point))

theorem polarDiskInverse_continuous : Continuous polarDiskInverse := by
  have base : Continuous (fun point : PuncturedDisk => point.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact (base.norm.subtype_mk _).prodMk (unitPlaneAngle_continuous.comp normalizedDiskDirection_continuous)

theorem polarDiskInverse_left : Function.LeftInverse polarDiskInverse polarDiskPoint := by
  intro argument
  apply Prod.ext
  · apply Subtype.ext
    exact polarDiskValue_norm argument
  · apply unitDiskCircle_injective
    rw [show (polarDiskInverse (polarDiskPoint argument)).2 =
      unitPlaneAngle (normalizedDiskDirection (polarDiskPoint argument)) from rfl,
      unitDiskCircle_unitPlaneAngle]
    change ‖polarDiskValue argument‖⁻¹ • polarDiskValue argument = unitDiskCircle argument.2
    rw [polarDiskValue_norm, polarDiskValue, smul_smul, inv_mul_cancel₀ argument.1.property.1.ne', one_smul]

theorem polarDiskInverse_right : Function.RightInverse polarDiskInverse polarDiskPoint := by
  intro point
  apply Subtype.ext
  apply Subtype.ext
  change ‖point.val.val‖ • unitDiskCircle (unitPlaneAngle (normalizedDiskDirection point)) = point.val.val
  rw [unitDiskCircle_unitPlaneAngle]
  change ‖point.val.val‖ • (‖point.val.val‖⁻¹ • point.val.val) = point.val.val
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr point.property), one_smul]

/-- One actual homeomorphism describes all radii 0<r≤1, including the boundary
leaf and excluding exactly the zero disk. -/
def polarDiskHomeomorph : PolarDiskDomain ≃ₜ PuncturedDisk where
  toFun := polarDiskPoint
  invFun := polarDiskInverse
  left_inv := polarDiskInverse_left
  right_inv := polarDiskInverse_right
  continuous_toFun := polarDiskPoint_continuous
  continuous_invFun := polarDiskInverse_continuous

end Grad.PhysicalGeometry
