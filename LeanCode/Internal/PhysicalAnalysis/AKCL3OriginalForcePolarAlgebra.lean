import AKCL2LiteralCovariantForceCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped BigOperators
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.SourceCollarFullSource Grad.ActualSmoothPhysicalField
open Grad.ActualCartesianEquations Grad.ActualDeterminantEquations Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.OriginalKernelHomogeneousGraph Grad.Constraints Grad.SourceCollar

 def originalPairCircle {parameters : PhaseParameters} (first second : ACore parameters 1)
    (radius : ℝ) (nonnegative : 0≤radius) (bounded : radius≤1) (angles : ℝ×ℝ) : ComplexEuclidean 3 :=
  WithLp.toLp 2 ![coreValue first (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 nonnegative bounded) angles.2 0,
    coreValue second (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 nonnegative bounded) angles.2 0,0]

 theorem originalPairCircle_polar {parameters : PhaseParameters} (first second : ACore parameters 1)
    (radius : ℝ) (positive : 0<radius) (bounded : radius≤1) (angles : ℝ×ℝ) :
    originalPairCircle first second radius positive.le bounded angles=
      cartesianCovariantValue angles.1 (WithLp.toLp 2 ![
        (radius : ℂ)⁻¹ * coreValue (coordinateCore parameters 0 first+coordinateCore parameters 1 second)
          (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 positive.le bounded) angles.2 0,
        (radius : ℂ)⁻¹ * coreValue (coordinateCore parameters 0 second-coordinateCore parameters 1 first)
          (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 positive.le bounded) angles.2 0,0]) := by
  let point := Grad.SourceCollarDivision.polarClosedPoint radius angles.1 positive.le bounded
  let x := coreValue first point angles.2 0
  let y := coreValue second point angles.2 0
  have coordinates0 : point.val 0=radius*Real.cos angles.1 := by
    simp [point,Grad.SourceCollarDivision.polarClosedPoint,polarPlane,Grad.BoundaryTrace.collarPlane]
  have coordinates1 : point.val 1=radius*Real.sin angles.1 := by
    simp [point,Grad.SourceCollarDivision.polarClosedPoint,polarPlane,Grad.BoundaryTrace.collarPlane]
  have radial : coreValue (coordinateCore parameters 0 first+coordinateCore parameters 1 second) point angles.2 0=
      (radius : ℂ)*((Real.cos angles.1 : ℂ)*x+(Real.sin angles.1 : ℂ)*y) := by
    rw [coreValue_add,coreValue_coordinate,coreValue_coordinate]
    change (point.val 0 : ℂ)*x+(point.val 1 : ℂ)*y=_
    rw [coordinates0,coordinates1,Complex.ofReal_mul,Complex.ofReal_mul]
    ring
  have angular : coreValue (coordinateCore parameters 0 second-coordinateCore parameters 1 first) point angles.2 0=
      (radius : ℂ)*(-(Real.sin angles.1 : ℂ)*x+(Real.cos angles.1 : ℂ)*y) := by
    rw [Grad.GaugeCoefficients.Physical.RadialLedger.coreValue_subtract,coreValue_coordinate,coreValue_coordinate]
    change (point.val 0 : ℂ)*y-(point.val 1 : ℂ)*x=_
    rw [coordinates0,coordinates1,Complex.ofReal_mul,Complex.ofReal_mul]
    ring
  change WithLp.toLp 2 ![x,y,0]=cartesianCovariantValue angles.1 (WithLp.toLp 2 ![
    (radius : ℂ)⁻¹ * coreValue (coordinateCore parameters 0 first+coordinateCore parameters 1 second) point angles.2 0,
    (radius : ℂ)⁻¹ * coreValue (coordinateCore parameters 0 second-coordinateCore parameters 1 first) point angles.2 0,0])
  rw [radial,angular,inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr positive.ne'),
    inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr positive.ne'),cartesianCovariantValue_apply]
  have circle : (Real.sin angles.1 : ℂ)^2+(Real.cos angles.1 : ℂ)^2=1 := by exact_mod_cast Real.sin_sq_add_cos_sq angles.1
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · change x=(Real.cos angles.1 : ℂ)*((Real.cos angles.1 : ℂ)*x+(Real.sin angles.1 : ℂ)*y)-
      (Real.sin angles.1 : ℂ)*(-(Real.sin angles.1 : ℂ)*x+(Real.cos angles.1 : ℂ)*y)
    linear_combination -x*circle
  · change y=(Real.sin angles.1 : ℂ)*((Real.cos angles.1 : ℂ)*x+(Real.sin angles.1 : ℂ)*y)+
      (Real.cos angles.1 : ℂ)*(-(Real.sin angles.1 : ℂ)*x+(Real.cos angles.1 : ℂ)*y)
    linear_combination -y*circle
  · rfl

end Grad.OriginalCoreRealization
