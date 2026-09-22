import AKAT6SameCartesianXiGradient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators
namespace Grad.ActualCartesianEquations
open Grad.ClosedJets Grad.ActualSmoothPhysicalField Grad.SourceCollar

/-- The planar part in the fixed Cartesian covariant frame. -/
def planarPart (value : ComplexEuclidean 3) : ComplexEuclidean 3 :=
  WithLp.toLp 2 ![value 0,value 1,0]

/-- The literal nonsingular AM18 expression before its radial mean projection. -/
def cartesianForceValue (gradient rotation covariant correction : ComplexEuclidean 3) : ComplexEuclidean 3 :=
  planarPart (gradient-rotation-polarQuarter covariant+correction)

theorem cartesianForceValue_polar (angle : ℝ) (covariant rotated correction : ComplexEuclidean 3)
    (radial angular : ℂ) :
    cartesianForceValue (cartesianCovariantValue angle (WithLp.toLp 2 ![radial,angular,0]))
      (cartesianCovariantValue angle (rotated + polarQuarter covariant))
      (cartesianCovariantValue angle covariant) correction =
      cartesianCovariantValue angle (WithLp.toLp 2 ![
        radial-rotated 0+2*covariant 1+
          ((Real.cos angle : ℂ)*correction 0+(Real.sin angle : ℂ)*correction 1),
        angular-rotated 1-2*covariant 0+
          (-(Real.sin angle : ℂ)*correction 0+(Real.cos angle : ℂ)*correction 1),0]) := by
  have circle : (Real.sin angle : ℂ)^2+(Real.cos angle : ℂ)^2=1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq angle
  simp only [cartesianForceValue,cartesianCovariantValue_apply,planarPart,polarQuarter]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · dsimp
    linear_combination -correction 0 * circle
  · dsimp
    linear_combination -correction 1 * circle
  · simp

/-- The correction vector is exactly twice the transposed rotated original
frame acting on SAME U; its polar components are the two original contractions. -/
theorem cartesianForceValue_matrix_polar (angle : ℝ) (covariant rotated : ComplexEuclidean 3)
    (radial angular : ℂ) (matrix : Matrix (Fin 3) (Fin 3) ℂ) (physical : ComplexEuclidean 3) :
    cartesianForceValue (cartesianCovariantValue angle (WithLp.toLp 2 ![radial,angular,0]))
      (cartesianCovariantValue angle (rotated + polarQuarter covariant))
      (cartesianCovariantValue angle covariant) ((2 : ℂ) • WithLp.toLp 2 (matrix.mulVec physical)) =
      cartesianCovariantValue angle (WithLp.toLp 2 ![
        radial-rotated 0+2*covariant 1+matrixPairing ((2 : ℂ) • physicalRadialVector angle) matrix physical,
        angular-rotated 1-2*covariant 0+matrixPairing ((2 : ℂ) • physicalTangentialVector angle) matrix physical,0]) := by
  rw [cartesianForceValue_polar]
  congr 1
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [matrixPairing,physicalRadialVector,physicalTangentialVector,dotProduct,Fin.sum_univ_three]
  all_goals ring

end Grad.ActualCartesianEquations
