import TameTangentBridge

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The literal planar dot convolution `(τ·η)_n = Σ_m τ_m · η_{n-m}` as a
sum of component products in the convolution ring, the quadratic map
`x(τ) = τ·τ/2`, and the exact quadratic curve identity feeding the root
Taylor calculus. -/

variable {parameters : PhaseParameters}

instance : Algebra ℂ (TameCoefficient parameters) :=
  Algebra.ofModule (fun scalar first second => tameSmul_mul scalar first second)
    (fun scalar first second => tameMul_smul scalar first second)

/-- The planar dot convolution through the component products. -/
def tangentDot (first second : TangentCoefficient parameters) :
    TameCoefficient parameters :=
  tangentComponent first 0 * tangentComponent second 0 +
    tangentComponent first 1 * tangentComponent second 1

theorem tangentDot_comm (first second : TangentCoefficient parameters) :
    tangentDot first second = tangentDot second first := by
  rw [tangentDot, tangentDot, mul_comm (tangentComponent first 0),
    mul_comm (tangentComponent first 1)]

theorem tangentDot_add_left (first second third : TangentCoefficient parameters) :
    tangentDot (first + second) third = tangentDot first third + tangentDot second third := by
  rw [tangentDot, tangentDot, tangentDot, tangentComponent_add, tangentComponent_add]
  ring

theorem tangentDot_smul_left (scalar : ℂ) (first second : TangentCoefficient parameters) :
    tangentDot (scalar • first) second = scalar • tangentDot first second := by
  rw [tangentDot, tangentDot, tangentComponent_smul, tangentComponent_smul,
    tameSmul_mul, tameSmul_mul, smul_add]

/-- The graded one-high envelope bound of the dot convolution. -/
theorem tangentDot_envelope_le (grade : ℕ) (first second : TangentCoefficient parameters) :
    coefficientEnvelope grade (tangentDot first second) ≤
      (2 : ℝ) ^ (grade + 1) *
        (tangentPlanarEnvelope grade first * tangentPlanarEnvelope 0 second +
          tangentPlanarEnvelope 0 first * tangentPlanarEnvelope grade second) := by
  have component_bound : ∀ (index : Fin 2),
      coefficientEnvelope grade
        (tangentComponent first index * tangentComponent second index) ≤
      (2 : ℝ) ^ grade *
        (tangentPlanarEnvelope grade first * tangentPlanarEnvelope 0 second +
          tangentPlanarEnvelope 0 first * tangentPlanarEnvelope grade second) := by
    intro index
    apply (tameMul_envelope_le grade _ _).trans
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) grade)
    apply add_le_add
    · exact mul_le_mul (tangentComponent_envelope_le grade first index)
        (tangentComponent_envelope_le 0 second index)
        (coefficientEnvelope_nonneg 0 _) (tangentPlanarEnvelope_nonneg grade first)
    · exact mul_le_mul (tangentComponent_envelope_le 0 first index)
        (tangentComponent_envelope_le grade second index)
        (coefficientEnvelope_nonneg grade _) (tangentPlanarEnvelope_nonneg 0 first)
  calc coefficientEnvelope grade (tangentDot first second)
      ≤ coefficientEnvelope grade
          (tangentComponent first 0 * tangentComponent second 0) +
        coefficientEnvelope grade
          (tangentComponent first 1 * tangentComponent second 1) :=
        coefficientEnvelope_add_le grade _ _
    _ ≤ (2 : ℝ) ^ grade *
          (tangentPlanarEnvelope grade first * tangentPlanarEnvelope 0 second +
            tangentPlanarEnvelope 0 first * tangentPlanarEnvelope grade second) +
        (2 : ℝ) ^ grade *
          (tangentPlanarEnvelope grade first * tangentPlanarEnvelope 0 second +
            tangentPlanarEnvelope 0 first * tangentPlanarEnvelope grade second) :=
        add_le_add (component_bound 0) (component_bound 1)
    _ = _ := by ring

/-- The sharp grade-zero bound of the dot convolution. -/
theorem tangentDot_envelope_zero_le (first second : TangentCoefficient parameters) :
    coefficientEnvelope 0 (tangentDot first second) ≤
      2 * (tangentPlanarEnvelope 0 first * tangentPlanarEnvelope 0 second) := by
  have component_bound : ∀ (index : Fin 2),
      coefficientEnvelope 0
        (tangentComponent first index * tangentComponent second index) ≤
      tangentPlanarEnvelope 0 first * tangentPlanarEnvelope 0 second := by
    intro index
    apply (tameMul_envelope_zero_le _ _).trans
    exact mul_le_mul (tangentComponent_envelope_le 0 first index)
      (tangentComponent_envelope_le 0 second index)
      (coefficientEnvelope_nonneg 0 _) (tangentPlanarEnvelope_nonneg 0 first)
  calc coefficientEnvelope 0 (tangentDot first second)
      ≤ coefficientEnvelope 0
          (tangentComponent first 0 * tangentComponent second 0) +
        coefficientEnvelope 0
          (tangentComponent first 1 * tangentComponent second 1) :=
        coefficientEnvelope_add_le 0 _ _
    _ ≤ tangentPlanarEnvelope 0 first * tangentPlanarEnvelope 0 second +
        tangentPlanarEnvelope 0 first * tangentPlanarEnvelope 0 second :=
        add_le_add (component_bound 0) (component_bound 1)
    _ = _ := by ring

/-- The literal quadratic coefficient `x(τ) = τ·τ/2`. -/
def tangentQuadratic (family : TangentCoefficient parameters) :
    TameCoefficient parameters :=
  ((2 : ℂ))⁻¹ • tangentDot family family

/-- Smallness of the quadratic on the strict planar unit ball. -/
theorem tangentQuadratic_small {family : TangentCoefficient parameters}
    (small : tangentPlanarEnvelope 0 family < 1) :
    coefficientEnvelope 0 (tangentQuadratic family) < 1 := by
  have planar_nonneg := tangentPlanarEnvelope_nonneg 0 family
  calc coefficientEnvelope 0 (tangentQuadratic family)
      = ‖((2 : ℂ))⁻¹‖ * coefficientEnvelope 0 (tangentDot family family) := by
        rw [tangentQuadratic, coefficientEnvelope_smul]
    _ ≤ ‖((2 : ℂ))⁻¹‖ *
        (2 * (tangentPlanarEnvelope 0 family * tangentPlanarEnvelope 0 family)) :=
        mul_le_mul_of_nonneg_left (tangentDot_envelope_zero_le family family)
          (norm_nonneg _)
    _ = tangentPlanarEnvelope 0 family * tangentPlanarEnvelope 0 family := by
        rw [norm_inv, Complex.norm_ofNat]
        ring
    _ < 1 := by nlinarith

/-- The exact quadratic curve identity: shifting the tangential family
moves the quadratic along the literal root curve. -/
theorem tangentQuadratic_curve (family direction : TangentCoefficient parameters)
    (t : ℝ) :
    tangentQuadratic (family + (t : ℂ) • direction) =
      rootCurvePoint (tangentQuadratic family) (tangentDot family direction)
        (((2 : ℂ))⁻¹ • tangentDot direction direction) t := by
  rw [rootCurvePoint, tangentQuadratic, tangentQuadratic, tangentDot, tangentDot, tangentDot,
    tangentDot]
  rw [tangentComponent_add, tangentComponent_add, tangentComponent_smul,
    tangentComponent_smul]
  set baseZero := tangentComponent family 0
  set baseOne := tangentComponent family 1
  set directionZero := tangentComponent direction 0
  set directionOne := tangentComponent direction 1
  have expand : (baseZero + (t : ℂ) • directionZero) * (baseZero + (t : ℂ) • directionZero) +
      (baseOne + (t : ℂ) • directionOne) * (baseOne + (t : ℂ) • directionOne) =
      (baseZero * baseZero + baseOne * baseOne) +
        ((2 : ℂ) * (t : ℂ)) • (baseZero * directionZero + baseOne * directionOne) +
        (((t : ℂ)) ^ 2) • (directionZero * directionZero + directionOne * directionOne) := by
    have mul_comm_zero : directionZero * baseZero = baseZero * directionZero := mul_comm _ _
    have mul_comm_one : directionOne * baseOne = baseOne * directionOne := mul_comm _ _
    rw [mul_add, mul_add, add_mul, add_mul, add_mul, add_mul]
    rw [tameMul_smul, tameMul_smul, tameSmul_mul, tameSmul_mul, tameSmul_mul, tameSmul_mul]
    rw [tameMul_smul, tameMul_smul, smul_smul, smul_smul]
    rw [mul_comm_zero, mul_comm_one, pow_two]
    simp only [two_mul, add_smul, smul_add]
    abel
  have scalar_one : ((2 : ℂ))⁻¹ * ((2 : ℂ) * (t : ℂ)) = (t : ℂ) := by ring
  have scalar_two : ((2 : ℂ))⁻¹ * ((t : ℂ)) ^ 2 = ((t : ℂ)) ^ 2 * ((2 : ℂ))⁻¹ := by ring
  rw [expand, smul_add, smul_add, smul_smul, smul_smul, scalar_one, scalar_two,
    ← smul_smul]

end Grad.NonlinearQuotientBounds
