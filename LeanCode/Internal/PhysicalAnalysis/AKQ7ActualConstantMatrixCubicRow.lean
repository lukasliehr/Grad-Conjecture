import AKQ5CubicComplementAndDivergence
import AKQ6ReferenceCubicMatrixInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CartesianScalarElimination
open Grad.NonlinearQuotientBounds

def quadraticValueMap (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (coefficients : QuadraticPlanarCoefficients) : QuadraticPlanarCoefficients :=
  fun index => mapping (coefficients index)

theorem quadraticPlanarJet_valueMap (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (coefficients : QuadraticPlanarCoefficients) :
    valueMapJet mapping (quadraticPlanarJet coefficients) = quadraticPlanarJet (quadraticValueMap mapping coefficients) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [valueMapJet_value,quadraticPlanarJet_value,quadraticValueMap,map_add]
  exact (by simp only [← Complex.coe_smul,map_smul])

def cubicDeterminantLinear (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) :
    ComplexEuclidean 2 →ₗ[ℂ] ComplexEuclidean 2 where
  toFun linear := quadraticDivergenceCoefficients
    (quadraticValueMap mapping (cubicComplementVectorCoefficients linear))
  map_add' first second := by
    have coefficients : cubicComplementVectorCoefficients (first + second) =
        cubicComplementVectorCoefficients first + cubicComplementVectorCoefficients second := by
      funext index
      apply PiLp.ext
      intro component
      fin_cases index <;> fin_cases component <;> simp [cubicComplementVectorCoefficients] <;> ring
    rw [coefficients]
    apply PiLp.ext
    intro component
    fin_cases component <;> simp [quadraticDivergenceCoefficients,quadraticValueMap,map_add] <;> ring
  map_smul' scalar linear := by
    change quadraticDivergenceCoefficients (quadraticValueMap mapping (cubicComplementVectorCoefficients (scalar • linear))) =
      scalar • quadraticDivergenceCoefficients (quadraticValueMap mapping (cubicComplementVectorCoefficients linear))
    have coefficients : cubicComplementVectorCoefficients (scalar • linear) =
        scalar • cubicComplementVectorCoefficients linear := by
      funext index
      apply PiLp.ext
      intro component
      fin_cases index <;> fin_cases component <;> simp [cubicComplementVectorCoefficients] <;> ring
    rw [coefficients]
    apply PiLp.ext
    intro component
    fin_cases component <;> simp [quadraticDivergenceCoefficients,quadraticValueMap,map_smul] <;> ring

/-- The two-dimensional constant-axis determinant matrix, defined by the
actual divergence of K times the already verified cubic planar lift. -/
def cubicDeterminantOperator (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) :
    ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2 :=
  (cubicDeterminantLinear mapping).toContinuousLinearMap

theorem cubicDeterminantOperator_actual (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (linear : ComplexEuclidean 2) (point : ClosedDisk) :
    (vectorDivJet (valueMapJet mapping (cubicPlanarLift (cubicComplementCoefficients linear)))).value point 0 =
      (point.val 0 : ℂ) * cubicDeterminantOperator mapping linear 0 +
        (point.val 1 : ℂ) * cubicDeterminantOperator mapping linear 1 := by
  rw [cubicPlanarLift,cubicComplementVector_is_inverse,quadraticPlanarJet_valueMap,quadraticPlanarJet_divergence_value]
  rfl

theorem cubicDeterminantOperator_reference :
    cubicDeterminantOperator (ContinuousLinearMap.id ℂ (ComplexEuclidean 2)) = referenceCubicOperator := by
  apply ContinuousLinearMap.ext
  intro linear
  exact cubicComplement_divergence_coefficients linear

/-- The reference inverse solves the literal constant-axis determinant
equation, with the exact 3/8 norm already established independently. -/
theorem referenceCubicInverse_actual (value : ComplexEuclidean 2) (point : ClosedDisk) :
    (vectorDivJet (cubicPlanarLift (cubicComplementCoefficients (referenceCubicInverse value)))).value point 0 =
      (point.val 0 : ℂ) * value 0 + (point.val 1 : ℂ) * value 1 := by
  rw [cubicPlanarLift,cubicComplementVector_is_inverse,quadraticPlanarJet_divergence_value,
    cubicComplement_divergence_coefficients]
  change (point.val 0 : ℂ) * referenceCubicOperator (referenceCubicInverse value) 0 +
    (point.val 1 : ℂ) * referenceCubicOperator (referenceCubicInverse value) 1 = _
  rw [referenceCubicOperator_inverse]

end Grad.FinitePhysicalJetLift
