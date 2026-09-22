import AKQ4CubicGradientAndForcedPlanarRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.NonlinearQuotientBounds Grad.CartesianScalarElimination

/-- I3 ell=(y1²+y2²)ell in literal homogeneous cubic coefficients. -/
def cubicComplementCoefficients (linear : ComplexEuclidean 2) : CubicScalarCoefficients :=
  ![linear 0,linear 1,linear 0,linear 1]

def cubicComplementVectorCoefficients (linear : ComplexEuclidean 2) : QuadraticPlanarCoefficients :=
  ![WithLp.toLp 2 ![(5 / 3 : ℂ) * linear 1,-(7 / 3 : ℂ) * linear 0],
    WithLp.toLp 2 ![(2 / 3 : ℂ) * linear 0,-(2 / 3 : ℂ) * linear 1],
    WithLp.toLp 2 ![(7 / 3 : ℂ) * linear 1,-(5 / 3 : ℂ) * linear 0]]

/-- The two supplied cubic monomial columns are checked simultaneously with
their exact signs, and hence for every linear combination. -/
theorem cubicComplementVector_operator (linear : ComplexEuclidean 2) :
    quadraticPlanarOperator (cubicComplementVectorCoefficients linear) =
      cubicGradientCoefficients (cubicComplementCoefficients linear) := by
  funext index
  apply PiLp.ext
  intro component
  fin_cases index <;> fin_cases component <;>
    simp [quadraticPlanarOperator,quadraticRotation,quadraticQuarterTurn,quarterValueMap,quarterValueLinear,
      cubicComplementVectorCoefficients,cubicGradientCoefficients,cubicComplementCoefficients] <;> ring

theorem cubicComplementVector_is_inverse (linear : ComplexEuclidean 2) :
    quadraticPlanarInverse (cubicGradientCoefficients (cubicComplementCoefficients linear)) =
      cubicComplementVectorCoefficients linear :=
  (congrArg quadraticPlanarInverse (cubicComplementVector_operator linear)).symm.trans
    (quadraticPlanarInverse_operator (cubicComplementVectorCoefficients linear))

theorem cubicPlanarLift_complement_value (linear : ComplexEuclidean 2) (point : ClosedDisk) :
    (cubicPlanarLift (cubicComplementCoefficients linear)).value point =
      WithLp.toLp 2 ![
        ((5 / 3 : ℂ) * (point.val 0 : ℂ) ^ 2 + (7 / 3 : ℂ) * (point.val 1 : ℂ) ^ 2) * linear 1 +
          (2 / 3 : ℂ) * (point.val 0 : ℂ) * (point.val 1 : ℂ) * linear 0,
        -((7 / 3 : ℂ) * (point.val 0 : ℂ) ^ 2 + (5 / 3 : ℂ) * (point.val 1 : ℂ) ^ 2) * linear 0 -
          (2 / 3 : ℂ) * (point.val 0 : ℂ) * (point.val 1 : ℂ) * linear 1] := by
  rw [cubicPlanarLift,cubicComplementVector_is_inverse,quadraticPlanarJet_value]
  apply PiLp.ext
  intro component
  fin_cases component <;> simp [cubicComplementVectorCoefficients,Complex.real_smul] <;> ring

/-- Coefficients of the actual ordinary divergence of a quadratic vector. -/
def quadraticDivergenceCoefficients (coefficients : QuadraticPlanarCoefficients) : ComplexEuclidean 2 :=
  WithLp.toLp 2 ![2 * coefficients 0 0 + coefficients 1 1,coefficients 1 0 + 2 * coefficients 2 1]

theorem quadraticPlanarJet_divergence_value (coefficients : QuadraticPlanarCoefficients) (point : ClosedDisk) :
    (vectorDivJet (quadraticPlanarJet coefficients)).value point 0 =
      (point.val 0 : ℂ) * quadraticDivergenceCoefficients coefficients 0 +
        (point.val 1 : ℂ) * quadraticDivergenceCoefficients coefficients 1 := by
  rw [vectorDivJet_value,quadraticPlanarJet_partial_value,quadraticPlanarJet_partial_value]
  simp [quadraticDivergenceCoefficients,Complex.real_smul]
  ring

/-- D_I=(8/3)R on the chosen linear complement. R acts on linear
coefficients as -J, so its two output columns have signs (-8y2/3,8y1/3). -/
theorem cubicComplement_divergence_coefficients (linear : ComplexEuclidean 2) :
    quadraticDivergenceCoefficients (cubicComplementVectorCoefficients linear) =
      (-(8 / 3 : ℂ)) • quarterValueMap linear := by
  apply PiLp.ext
  intro component
  fin_cases component <;>
    simp [quadraticDivergenceCoefficients,cubicComplementVectorCoefficients,quarterValueMap,quarterValueLinear] <;> ring

end Grad.FinitePhysicalJetLift
