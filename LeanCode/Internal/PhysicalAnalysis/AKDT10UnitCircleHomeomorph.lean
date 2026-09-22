import AKDT9CircleCoordinate

noncomputable section
open Set
open scoped ContDiff Topology

namespace Grad.PhysicalGeometry
open Grad.MainTarget

abbrev UnitPlaneCircle := {point : Plane // ‖point‖ = 1}

def planeToComplex (point : Plane) : ℂ := ⟨point 0, point 1⟩

theorem planeToComplex_norm (point : Plane) : ‖planeToComplex point‖ = ‖point‖ := by
  rw [Complex.norm_def, PiLp.norm_eq_of_L2, Fin.sum_univ_two]
  simp [planeToComplex, Complex.normSq_apply, Real.norm_eq_abs, pow_two]

theorem planeToComplex_continuous : Continuous planeToComplex := by
  have identity : planeToComplex = fun point : Plane => (point 0 : ℂ) + (point 1 : ℂ) * Complex.I := by
    funext point
    apply Complex.ext <;> simp [planeToComplex]
  rw [identity]
  fun_prop

def unitPlaneToCircle (point : UnitPlaneCircle) : Circle :=
  ⟨planeToComplex point.val, by
    have unit := (planeToComplex_norm point.val).trans point.property
    simpa [Submonoid.unitSphere, Metric.mem_sphere, dist_zero_right] using unit⟩

theorem unitPlaneToCircle_continuous : Continuous unitPlaneToCircle :=
  (planeToComplex_continuous.comp continuous_subtype_val).subtype_mk _

def unitPlaneAngle (point : UnitPlaneCircle) : CellCircle :=
  (AddCircle.homeomorphCircle (by positivity : (2 * Real.pi : ℝ) ≠ 0)).symm (unitPlaneToCircle point)

theorem unitPlaneAngle_continuous : Continuous unitPlaneAngle :=
  (AddCircle.homeomorphCircle (by positivity : (2 * Real.pi : ℝ) ≠ 0)).symm.continuous.comp unitPlaneToCircle_continuous

theorem unitDiskCircle_unitPlaneAngle (point : UnitPlaneCircle) : unitDiskCircle (unitPlaneAngle point) = point.val := by
  have same := (AddCircle.homeomorphCircle (by positivity : (2 * Real.pi : ℝ) ≠ 0)).apply_symm_apply (unitPlaneToCircle point)
  rw [AddCircle.homeomorphCircle_apply] at same
  change AddCircle.toCircle (unitPlaneAngle point) = unitPlaneToCircle point at same
  ext coordinate
  fin_cases coordinate <;> simp [unitDiskCircle, same, unitPlaneToCircle, planeToComplex]

/-- The genuine quotient circle is homeomorphic to the unit planar circle,
with the continuous angular inverse inherited from the complex unit circle. -/
def unitCircleHomeomorph : CellCircle ≃ₜ UnitPlaneCircle where
  toFun angle := ⟨unitDiskCircle angle, unitDiskCircle_norm angle⟩
  invFun := unitPlaneAngle
  left_inv angle := unitDiskCircle_injective (unitDiskCircle_unitPlaneAngle ⟨unitDiskCircle angle, unitDiskCircle_norm angle⟩)
  right_inv point := Subtype.ext (unitDiskCircle_unitPlaneAngle point)
  continuous_toFun := unitDiskCircle_continuous.subtype_mk _
  continuous_invFun := unitPlaneAngle_continuous

end Grad.PhysicalGeometry
