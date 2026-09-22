import GC14SeedMatrix
import GC12SeriesEquation

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity

def SeedSpatiallyConstant {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension) : Prop :=
  ∀ (cell : ℤ) (index : DerivativeIndex grade), 0 < derivativeOrder index →
    ∀ point : ClosedDisk, coefficientDerivative coefficient cell index point = 0

theorem seedConstantCell_spatial (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ} (cell : ℤ) (value : OperatorValue inputDimension outputDimension) :
    SeedSpatiallyConstant (seedConstantCell L sigma gamma ell grade cell value) := by
  intro other index positive point
  rw [seedConstantCell_derivative]
  simp [Nat.ne_of_gt positive]

theorem SeedSpatiallyConstant.add {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    {first second : Coefficient L sigma gamma ell grade inputDimension outputDimension}
    (firstConstant : SeedSpatiallyConstant first) (secondConstant : SeedSpatiallyConstant second) :
    SeedSpatiallyConstant (first + second) := by
  intro cell index positive point
  rw [coefficientDerivative_add_apply, firstConstant cell index positive point,
    secondConstant cell index positive point, add_zero]

theorem SeedSpatiallyConstant.smul {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    {coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension}
    (constant : SeedSpatiallyConstant coefficient) (scalar : ℂ) :
    SeedSpatiallyConstant (scalar • coefficient) := by
  intro cell index positive point
  rw [coefficientDerivative_smul_apply, constant cell index positive point]
  apply ContinuousLinearMap.ext
  intro vector
  simp

theorem seedConstant_sum {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    {Index : Type*} (indices : Finset Index)
    (coefficients : Index → Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (constant : ∀ item ∈ indices, SeedSpatiallyConstant (coefficients item)) :
    SeedSpatiallyConstant (∑ item ∈ indices, coefficients item) := by
  intro cell index positive point
  rw [seedDerivative_sum]
  exact Finset.sum_eq_zero fun item membership => constant item membership cell index positive point

theorem seedConstant_tsum {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    {Index : Type*} (coefficients : Index → Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (summability : Summable coefficients) (constant : ∀ item, SeedSpatiallyConstant (coefficients item)) :
    SeedSpatiallyConstant (∑' item, coefficients item) := by
  intro cell index positive point
  rw [seedDerivative_tsum coefficients summability]
  exact (tsum_congr fun item => constant item cell index positive point).trans (tsum_zero)

theorem seedConstant_composition {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension middleDimension outputDimension : ℕ}
    {outer : Coefficient L sigma gamma ell grade middleDimension outputDimension}
    {inner : Coefficient L sigma gamma ell grade inputDimension middleDimension}
    (outerConstant : SeedSpatiallyConstant outer) (innerConstant : SeedSpatiallyConstant inner) :
    SeedSpatiallyConstant (coefficientComposition admissible grade outer inner) := by
  intro cell index positive point
  rw [coefficientComposition_derivative]
  unfold formalCompositionDerivative
  refine (tsum_congr (g := fun _ : ℤ => (0 : OperatorValue inputDimension outputDimension)) ?_).trans (tsum_zero)
  intro first
  apply Finset.sum_eq_zero
  intro split _
  have orderIdentity := derivative_split_order index split
  by_cases lowerZero : derivativeOrder (lowerDerivativeIndex index split) = 0
  · rw [innerConstant (cell - first) (upperDerivativeIndex index split) (by omega) point]
    apply ContinuousLinearMap.ext
    intro vector
    simp
  · rw [outerConstant first (lowerDerivativeIndex index split) (by omega) point]
    apply ContinuousLinearMap.ext
    intro vector
    simp

theorem seedPower_spatial {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    {coefficient : Coefficient L sigma gamma ell grade dimension dimension}
    (constant : SeedSpatiallyConstant coefficient) (power : ℕ) :
    SeedSpatiallyConstant (gradedCoefficientPower admissible coefficient power) := by
  induction power with
  | zero => exact gradedIdentityCoefficient_positiveDerivative L sigma gamma ell grade dimension
  | succ power inductionHypothesis => exact seedConstant_composition admissible constant inductionHypothesis

theorem seedExponential_spatial {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    {coefficient : Coefficient L sigma gamma ell grade dimension dimension}
    (constant : SeedSpatiallyConstant coefficient) :
    SeedSpatiallyConstant (seedCoefficientExponential admissible coefficient) :=
  seedConstant_tsum _ (seedExponentialTerm_norm_summable admissible coefficient).of_norm
    (fun power => (seedPower_spatial admissible constant power).smul ((power.factorial : ℂ)⁻¹))

theorem seedAngleExponential_spatial {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (sign alpha delta parameter : ℝ) :
    SeedSpatiallyConstant (seedAngleExponential admissible grade sign alpha delta parameter) := by
  apply seedExponential_spatial
  apply seedConstant_sum
  intro mode _
  exact seedConstantCell_spatial L sigma gamma ell grade _ _

theorem seedScalarLift_spatial {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade : ℕ}
    (matrix : OperatorValue 2 2) {coefficient : Coefficient L sigma gamma ell grade 1 1}
    (constant : SeedSpatiallyConstant coefficient) :
    SeedSpatiallyConstant (seedScalarLift admissible matrix coefficient) := by
  apply seedConstant_sum
  intro coordinate _
  exact seedConstant_composition admissible (seedConstantCell_spatial _ _ _ _ _ _ _)
    (seedConstant_composition admissible constant (seedConstantCell_spatial _ _ _ _ _ _ _))

theorem seedMatrixDeviation_spatial {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (rho alpha delta parameter : ℝ) :
    SeedSpatiallyConstant (seedMatrixDeviationCoefficient admissible grade rho alpha delta parameter) :=
  (seedConstantCell_spatial _ _ _ _ _ _ _).add
    (((seedScalarLift_spatial admissible seedPlusMatrix (seedAngleExponential_spatial admissible grade 1 _ _ _)).add
      (seedScalarLift_spatial admissible seedMinusMatrix (seedAngleExponential_spatial admissible grade (-1) _ _ _))).smul _)

end Grad.GaugeCoefficients.Physical.Frame
