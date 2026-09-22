import AKAT2PolarCovariantDerivative
import AKAE3ExactCartesianPolarDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter
open scoped ContDiff
namespace Grad.ActualCartesianEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.PhysicalFamily
open Grad.ActualCartesianDescent Grad.ActualSmoothPhysicalField

/-- The genuine two Cartesian partials, embedded in the same three-component
covariant frame with zero toroidal component. -/
def planarGradientValue (derivative : SpatialPlane × ℝ →L[ℝ] ComplexEuclidean 1) : ComplexEuclidean 3 :=
  WithLp.toLp 2 ![derivative (spatialBasis 0,0) 0,derivative (spatialBasis 1,0) 0,0]

private theorem cartesianBasis_from_polar (angle : ℝ) :
    spatialBasis 0 = Real.cos angle • radialDirection angle -
      Real.sin angle • planeQuarterTurn (radialDirection angle) ∧
    spatialBasis 1 = Real.sin angle • radialDirection angle +
      Real.cos angle • planeQuarterTurn (radialDirection angle) := by
  constructor <;> apply PiLp.ext <;> intro coordinate <;> fin_cases coordinate <;>
    simp [spatialBasis,radialDirection,Grad.BoundaryTrace.collarPlane,planeQuarterTurn]
  all_goals nlinarith [Real.cos_sq_add_sin_sq angle]

/-- Exact polar-to-Cartesian gradient identity for an arbitrary genuine
Frechet derivative, before substituting any field equation. -/
theorem planarGradientValue_polar (derivative : SpatialPlane × ℝ →L[ℝ] ComplexEuclidean 1)
    (angle : ℝ) :
    planarGradientValue derivative = cartesianCovariantValue angle
      (WithLp.toLp 2 ![derivative (radialDirection angle,0) 0,
        derivative (planeQuarterTurn (radialDirection angle),0) 0,0]) := by
  have first := (cartesianBasis_from_polar angle).1
  have second := (cartesianBasis_from_polar angle).2
  have firstPair : (spatialBasis 0,(0 : ℝ)) =
      Real.cos angle • (radialDirection angle,(0 : ℝ)) -
        Real.sin angle • (planeQuarterTurn (radialDirection angle),(0 : ℝ)) := by
    apply Prod.ext
    · exact first
    · simp
  have secondPair : (spatialBasis 1,(0 : ℝ)) =
      Real.sin angle • (radialDirection angle,(0 : ℝ)) +
        Real.cos angle • (planeQuarterTurn (radialDirection angle),(0 : ℝ)) := by
    apply Prod.ext
    · exact second
    · simp
  have firstValue := congrArg derivative firstPair
  have secondValue := congrArg derivative secondPair
  rw [map_sub,map_smul,map_smul] at firstValue
  rw [map_add,map_smul,map_smul] at secondValue
  rw [cartesianCovariantValue_apply]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [planarGradientValue,firstValue,secondValue,Complex.real_smul]

/-- The radial and angular derivatives determine the actual Cartesian
partial derivatives of the SAME descended field on the punctured disk. -/
theorem cartesianPhysicalField_gradient_from_derivatives
    (field : ℝ × (ℝ × ℝ) → ComplexEuclidean 1) (lower upper : ℝ)
    (smooth : ContDiffOn ℝ ∞ field (Ioo lower upper ×ˢ (univ : Set (ℝ × ℝ))))
    (periodic : ∀ radius axial,Function.Periodic (fun polar => field (radius,polar,axial)) (2*Real.pi))
    (radius : ℝ) (positive : 0 < radius) (inside : radius ∈ Ioo lower upper) (polar axial : ℝ)
    (radial angular : ComplexEuclidean 1)
    (radialLaw : HasDerivAt (fun query => field (query,polar,axial)) radial radius)
    (angularLaw : HasDerivAt (fun query => field (radius,query,axial)) angular polar) :
    planarGradientValue (fderiv ℝ (cartesianPhysicalField field) (polarPlane (radius,polar),axial)) =
      cartesianCovariantValue polar (WithLp.toLp 2 ![radial 0,(radius : ℂ)⁻¹ * angular 0,0]) := by
  let derivative := fderiv ℝ (cartesianPhysicalField field) (polarPlane (radius,polar),axial)
  have radialSame : derivative (radialDirection polar,0) = radial :=
    (cartesianPhysicalField_radial_hasDerivAt field lower upper smooth periodic radius positive inside polar axial).unique radialLaw
  have angularSame : derivative (radius • planeQuarterTurn (radialDirection polar),0) = angular :=
    (cartesianPhysicalField_angular_hasDerivAt field lower upper smooth periodic radius positive inside polar axial).unique angularLaw
  have angularPair : (radius • planeQuarterTurn (radialDirection polar),(0 : ℝ)) =
      radius • (planeQuarterTurn (radialDirection polar),(0 : ℝ)) := by simp
  rw [angularPair,map_smul] at angularSame
  have unscaled : derivative (planeQuarterTurn (radialDirection polar),0) = radius⁻¹ • angular := by
    rw [← angularSame,smul_smul,inv_mul_cancel₀ positive.ne',one_smul]
  rw [planarGradientValue_polar,radialSame,unscaled]
  congr 1
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [Complex.real_smul,Complex.ofReal_inv]

end Grad.ActualCartesianEquations
