import AKBL6SameOriginalWeakEllipticRows
import AKBE8LiteralRadialProjectionFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped Interval
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets
open Grad.SourceCollarDivision Grad.BoundaryTrace Grad.ActualCartesianWeakEquations

 theorem startupPolar_rotation (radius angle shift : ℝ) :
    planeRotationEquiv shift (polarPlane (radius,angle)) = polarPlane (radius,shift+angle) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [planeRotationEquiv_apply,planeRotation,polarPlane,collarPlane,Real.cos_add,Real.sin_add] <;> ring

 theorem startupPolar_axis (radius angle : ℝ) :
    planeRotationEquiv angle (radius • spatialDirection 0) = polarPlane (radius,angle) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [planeRotationEquiv_apply,planeRotation,polarPlane,collarPlane,spatialDirection]

 theorem startupPolar_function_periodic {Value : Type*} (field : Spatial → Value) (radius : ℝ) :
    Function.Periodic (fun angle => field (polarPlane (radius,angle))) (2*Real.pi) := by
  intro angle
  exact congrArg field (by simpa using polarPlane_periodic (radius,angle))

/-- Literal polar Fourier mean zero gives the Cartesian orbit integral used
by the rough angular kernel. The proof changes only the starting angle and
normalization of a full period; no global continuity at the axis is assumed. -/
 theorem startupRawPolarMean_orbit {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (raw : Spatial → Value) (point : Spatial)
    (mean : angularCoefficient (fun angle => raw (polarPlane (‖point‖,angle))) 0 = 0) :
    (∫ angle in Icc (0 : ℝ) (2*Real.pi), raw (planeRotationEquiv angle point)) = 0 := by
  have periodic := startupPolar_function_periodic raw ‖point‖
  rw [originalAngularMean_interval _ periodic] at mean
  have unnormalized : (∫ angle in (0 : ℝ)..2*Real.pi, raw (polarPlane (‖point‖,angle))) = 0 :=
    (smul_eq_zero.mp mean).resolve_left (inv_ne_zero (by positivity : (2*Real.pi : ℝ) ≠ 0))
  obtain ⟨argument,polar⟩ := startupPoint_polar_rotation point
  rw [startupPolar_axis] at polar
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2*Real.pi)]
  have same : (fun angle => raw (planeRotationEquiv angle point)) =
      fun angle => raw (polarPlane (‖point‖,angle+argument)) := by
    funext angle
    calc
      _ = raw (planeRotationEquiv angle (polarPlane (‖point‖,argument))) :=
        congrArg (fun query => raw (planeRotationEquiv angle query)) polar.symm
      _ = _ := congrArg raw (startupPolar_rotation ‖point‖ argument angle)
  rw [same]
  let integrand := fun angle => raw (polarPlane (‖point‖,angle))
  change (∫ angle in (0 : ℝ)..2*Real.pi,integrand (angle+argument)) = 0
  rw [intervalIntegral.integral_comp_add_right]
  have shifted := periodic.intervalIntegral_add_eq argument 0
  simp only [zero_add] at shifted
  simpa only [add_zero,zero_add,add_comm,integrand] using shifted.trans unnormalized

 theorem startupPolar_dilation (scale radius angle : ℝ) :
    scale • polarPlane (radius,angle) = polarPlane (scale*radius,angle) := by
  rw [polarPlane_eq,polarPlane_eq,smul_smul]

/-- Exact scaled original scalar mean, preserving the original radius and
without introducing a mean hypothesis on a newly chosen L2 representative. -/
 theorem startupRawPolarMean_dilation {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (raw : Spatial → Value) (scale scalar : ℝ) (point : Spatial)
    (mean : angularCoefficient (fun angle => raw (polarPlane (scale*‖point‖,angle))) 0 = 0) :
    (∫ angle in Icc (0 : ℝ) (2*Real.pi), scalar • raw (scale • planeRotationEquiv angle point)) = 0 := by
  rw [integral_smul]
  apply smul_eq_zero.mpr
  right
  apply startupRawPolarMean_orbit (fun query => raw (scale • query)) point
  simpa only [startupPolar_dilation] using mean

end Grad.CartesianStartup
