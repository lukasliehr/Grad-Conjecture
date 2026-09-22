import AKQ1QuadraticPlanarInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.Constraints

/-- The verified complement matrix D_I=(8/3)R; on linear coefficients R=-J. -/
def referenceCubicOperator : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2 :=
  (-(8 / 3 : ℂ)) • quarterValueMap

def referenceCubicInverse : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2 :=
  (3 / 8 : ℂ) • quarterValueMap

theorem referenceCubicOperator_inverse (value : ComplexEuclidean 2) :
    referenceCubicOperator (referenceCubicInverse value) = value := by
  change (-(8 / 3 : ℂ)) • quarterValueMap ((3 / 8 : ℂ) • quarterValueMap value) = value
  rw [map_smul,quarterValueMap_square,smul_smul,smul_neg]
  norm_num

theorem referenceCubicInverse_operator (value : ComplexEuclidean 2) :
    referenceCubicInverse (referenceCubicOperator value) = value := by
  change (3 / 8 : ℂ) • quarterValueMap ((-(8 / 3 : ℂ)) • quarterValueMap value) = value
  rw [map_smul,quarterValueMap_square,smul_smul,smul_neg]
  norm_num

/-- Exact Euclidean norm, not a loose matrix-entry bound. -/
theorem referenceCubicInverse_norm (value : ComplexEuclidean 2) :
    ‖referenceCubicInverse value‖ = (3 / 8 : ℝ) * ‖value‖ := by
  have quarter : ‖quarterValueMap value‖ = ‖value‖ := quarterValue_norm value
  change ‖(3 / 8 : ℂ) • quarterValueMap value‖ = _
  rw [norm_smul,quarter]
  norm_num

theorem referenceCubicInverse_opNorm : ‖referenceCubicInverse‖ = (3 / 8 : ℝ) := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro value
    exact (referenceCubicInverse_norm value).le
  · have bound := referenceCubicInverse.le_opNorm (EuclideanSpace.single 0 (1 : ℂ))
    rw [referenceCubicInverse_norm] at bound
    simpa using bound

end Grad.FinitePhysicalJetLift
