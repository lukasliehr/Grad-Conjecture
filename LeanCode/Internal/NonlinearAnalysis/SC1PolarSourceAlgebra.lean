import AXF32PublicBoundary

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.SourceCollar

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState Grad.Constraints

/-- Reconstruct the Cartesian planar source from its unrestricted tangential
and radial polar components. The order is exactly BS32. -/
def polarSourceReconstruct (angle : ℝ) (tangential radial : ℂ) :
    ComplexEuclidean 2 :=
  tangential • polarTangentialVector angle + radial • polarRadialVector angle

theorem polarTangentialComponent_reconstruct (angle : ℝ) (tangential radial : ℂ) :
    polarTangentialComponent angle
      (polarSourceReconstruct angle tangential radial) = tangential := by
  unfold polarTangentialComponent polarSourceReconstruct
    polarTangentialVector polarRadialVector
  simp only [PiLp.add_apply, PiLp.smul_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul]
  have trig : ((Real.sin angle : ℂ) ^ 2 + (Real.cos angle : ℂ) ^ 2) = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq angle
  calc
    _ = (((Real.sin angle : ℂ) ^ 2 + (Real.cos angle : ℂ) ^ 2) * tangential) := by
      ring
    _ = tangential := by rw [trig, one_mul]

theorem polarRadialComponent_reconstruct (angle : ℝ) (tangential radial : ℂ) :
    polarRadialComponent angle
      (polarSourceReconstruct angle tangential radial) = radial := by
  unfold polarRadialComponent polarSourceReconstruct
    polarTangentialVector polarRadialVector
  simp only [PiLp.add_apply, PiLp.smul_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul]
  have trig : ((Real.sin angle : ℂ) ^ 2 + (Real.cos angle : ℂ) ^ 2) = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq angle
  calc
    _ = (((Real.sin angle : ℂ) ^ 2 + (Real.cos angle : ℂ) ^ 2) * radial) := by
      ring
    _ = radial := by rw [trig, one_mul]

/-- The two literal polar components recover every Cartesian planar source;
no condition is imposed on the tangential component `F0`. -/
theorem polarSourceReconstruct_components (angle : ℝ)
    (source : ComplexEuclidean 2) :
    polarSourceReconstruct angle (polarTangentialComponent angle source)
      (polarRadialComponent angle source) = source := by
  apply PiLp.ext
  intro coordinate
  have trig : ((Real.sin angle : ℂ) ^ 2 + (Real.cos angle : ℂ) ^ 2) = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq angle
  fin_cases coordinate
  · simp [polarSourceReconstruct, polarTangentialComponent,
      polarTangentialVector, polarRadialComponent, polarRadialVector]
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cos]
    calc
      _ = (((Real.sin angle : ℂ) ^ 2 + (Real.cos angle : ℂ) ^ 2) * source 0) := by
        ring
      _ = source 0 := by rw [trig, one_mul]
  · simp [polarSourceReconstruct, polarTangentialComponent,
      polarTangentialVector, polarRadialComponent, polarRadialVector]
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cos]
    calc
      _ = (((Real.sin angle : ℂ) ^ 2 + (Real.cos angle : ℂ) ^ 2) * source 1) := by
        ring
      _ = source 1 := by rw [trig, one_mul]

end Grad.SourceCollar
