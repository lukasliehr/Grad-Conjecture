import AKDT8ActualBoundaryFields
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

noncomputable section
open Set
open scoped ContDiff Topology

namespace Grad.PhysicalGeometry
open Grad.MainTarget

local instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- The actual angular quotient coordinate on the unit disk circle. -/
def unitDiskCircle (angle : CellCircle) : Plane :=
  WithLp.toLp 2 ![(AddCircle.toCircle angle : ℂ).re, (AddCircle.toCircle angle : ℂ).im]

theorem unitDiskCircle_norm (angle : CellCircle) : ‖unitDiskCircle angle‖ = 1 := by
  rw [PiLp.norm_eq_of_L2, Fin.sum_univ_two]
  change Real.sqrt (‖(AddCircle.toCircle angle : ℂ).re‖ ^ 2 +
    ‖(AddCircle.toCircle angle : ℂ).im‖ ^ 2) = 1
  simp only [Real.norm_eq_abs, sq_abs]
  simpa only [Complex.norm_def, Complex.normSq_apply, pow_two] using
    Circle.norm_coe (AddCircle.toCircle angle)

theorem unitDiskCircle_continuous : Continuous unitDiskCircle := by
  have circleContinuous : Continuous (fun angle : CellCircle => (AddCircle.toCircle angle : ℂ)) :=
    continuous_induced_dom.comp AddCircle.continuous_toCircle
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro coordinate
  fin_cases coordinate
  · exact Complex.continuous_re.comp circleContinuous
  · exact Complex.continuous_im.comp circleContinuous

theorem unitDiskCircle_coe (angle : ℝ) :
    unitDiskCircle (angle : CellCircle) = WithLp.toLp 2 ![Real.cos angle, Real.sin angle] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [unitDiskCircle, AddCircle.toCircle_apply_mk, Circle.coe_exp,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem unitDiskCircle_injective : Function.Injective unitDiskCircle := by
  intro first second equal
  apply AddCircle.injective_toCircle (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  apply Subtype.ext
  apply Complex.ext
  · exact congrArg (fun point : Plane => point 0) equal
  · exact congrArg (fun point : Plane => point 1) equal

/-- Every unit planar direction has its genuine quotient angle. -/
theorem unitDiskCircle_surjective (point : Plane) (unit : ‖point‖ = 1) :
    ∃ angle : CellCircle, unitDiskCircle angle = point := by
  let value : ℂ := ⟨point 0, point 1⟩
  have valueNorm : ‖value‖ = 1 := by
    rw [Complex.norm_def]
    have normFormula := PiLp.norm_eq_of_L2 point
    rw [Fin.sum_univ_two] at normFormula
    simpa [value, Complex.normSq_apply, Real.norm_eq_abs, sq_abs, pow_two] using normFormula.symm.trans unit
  let circle : Circle := ⟨value, by simpa [Submonoid.unitSphere, Metric.mem_sphere, dist_zero_right] using valueNorm⟩
  obtain ⟨angle, same⟩ := (AddCircle.homeomorphCircle (by positivity : (2 * Real.pi : ℝ) ≠ 0)).surjective circle
  rw [AddCircle.homeomorphCircle_apply] at same
  refine ⟨angle, ?_⟩
  ext coordinate
  fin_cases coordinate <;> simp [unitDiskCircle, same, circle, value]

end Grad.PhysicalGeometry
