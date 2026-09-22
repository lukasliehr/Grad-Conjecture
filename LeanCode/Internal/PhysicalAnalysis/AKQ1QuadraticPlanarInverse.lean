import AKO15ActualCompatibleFamilyVanishingTraces

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.Constraints Grad.Constraints.Gauges

/-- Coefficients of y1², y1*y2, y2², each with both planar components. -/
abbrev QuadraticPlanarCoefficients := Fin 3 → ComplexEuclidean 2

/-- Literal angular derivative on homogeneous quadratic planar polynomials. -/
def quadraticRotation : QuadraticPlanarCoefficients →ₗ[ℂ] QuadraticPlanarCoefficients where
  toFun coefficients := ![coefficients 1, (2 : ℂ) • coefficients 2 - (2 : ℂ) • coefficients 0, -coefficients 1]
  map_add' first second := by
    funext index
    fin_cases index <;> simp <;> module
  map_smul' scalar coefficients := by
    funext index
    fin_cases index <;> simp
    module

def quadraticQuarterTurn : QuadraticPlanarCoefficients →ₗ[ℂ] QuadraticPlanarCoefficients where
  toFun coefficients index := quarterValueMap (coefficients index)
  map_add' first second := by funext index; exact map_add quarterValueMap _ _
  map_smul' scalar coefficients := by funext index; exact map_smul quarterValueMap _ _

/-- The actual leading planar operator D=R+J on precisely the quadratic space. -/
def quadraticPlanarOperator : QuadraticPlanarCoefficients →ₗ[ℂ] QuadraticPlanarCoefficients :=
  quadraticRotation + quadraticQuarterTurn

/-- The finite inverse polynomial: D has only spin frequencies ±1 and ±3.
Both inverse identities below are verified directly on all six coefficients. -/
def quadraticPlanarInverse : QuadraticPlanarCoefficients →ₗ[ℂ] QuadraticPlanarCoefficients :=
  (-(1 / 9 : ℂ)) • (quadraticPlanarOperator.comp (quadraticPlanarOperator.comp quadraticPlanarOperator) +
    (10 : ℂ) • quadraticPlanarOperator)

theorem quadraticPlanarOperator_inverse (coefficients : QuadraticPlanarCoefficients) :
    quadraticPlanarOperator (quadraticPlanarInverse coefficients) = coefficients := by
  funext index
  apply PiLp.ext
  intro component
  fin_cases index <;> fin_cases component <;>
    simp [quadraticPlanarInverse,quadraticPlanarOperator,quadraticRotation,quadraticQuarterTurn,
      quarterValueMap,quarterValueLinear,Matrix.vecHead,Matrix.vecTail,
      PiLp.add_apply,PiLp.sub_apply,PiLp.neg_apply,PiLp.smul_apply] <;> ring

theorem quadraticPlanarInverse_operator (coefficients : QuadraticPlanarCoefficients) :
    quadraticPlanarInverse (quadraticPlanarOperator coefficients) = coefficients := by
  funext index
  apply PiLp.ext
  intro component
  fin_cases index <;> fin_cases component <;>
    simp [quadraticPlanarInverse,quadraticPlanarOperator,quadraticRotation,quadraticQuarterTurn,
      quarterValueMap,quarterValueLinear,Matrix.vecHead,Matrix.vecTail,
      PiLp.add_apply,PiLp.sub_apply,PiLp.neg_apply,PiLp.smul_apply] <;> ring

def quadraticPlanarEquivalence : QuadraticPlanarCoefficients ≃ₗ[ℂ] QuadraticPlanarCoefficients where
  toLinearMap := quadraticPlanarOperator
  invFun := quadraticPlanarInverse
  left_inv := quadraticPlanarInverse_operator
  right_inv := quadraticPlanarOperator_inverse

end Grad.FinitePhysicalJetLift
