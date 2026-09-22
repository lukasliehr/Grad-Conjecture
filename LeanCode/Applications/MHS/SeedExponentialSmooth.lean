import SeedExponentialOperator
import SeedOperatorCalculus

noncomputable section

set_option synthInstance.maxHeartbeats 200000

open scoped ContDiff

namespace Grad.Constraints.Seed

open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.Frame

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) (grade dimension : ℕ)

local instance seedComplexSpace : NormedSpace ℂ (Coefficient L sigma gamma ell grade dimension dimension) := inferInstance
local instance seedRealSpace : NormedSpace ℝ (Coefficient L sigma gamma ell grade dimension dimension) := inferInstance

theorem seedExponential_operator_formula (coefficient : Coefficient L sigma gamma ell grade dimension dimension) :
    seedCoefficientExponential admissible coefficient =
      operatorExponentialApply (E := Coefficient L sigma gamma ell grade dimension dimension) (leftCompositionOperator admissible grade dimension)
        (gradedIdentityCoefficient L sigma gamma ell grade dimension) coefficient := by
  have evaluated := operatorExponentialApply_hasSum
    (E := Coefficient L sigma gamma ell grade dimension dimension)
    (leftCompositionOperator admissible grade dimension)
    (gradedIdentityCoefficient L sigma gamma ell grade dimension) coefficient
  have termIdentity (power : ℕ) :
      ((power.factorial : ℂ)⁻¹) •
        (leftCompositionOperator admissible grade dimension coefficient ^ power)
          (gradedIdentityCoefficient L sigma gamma ell grade dimension) =
      seedExponentialTerm admissible coefficient power := by
    rw [leftCompositionOperator_power]
    rfl
  have exactSum : HasSum (seedExponentialTerm admissible coefficient)
      (operatorExponentialApply (E := Coefficient L sigma gamma ell grade dimension dimension) (leftCompositionOperator admissible grade dimension)
        (gradedIdentityCoefficient L sigma gamma ell grade dimension) coefficient) := by
    simpa only [termIdentity] using evaluated
  exact (seedExponentialTerm_norm_summable admissible coefficient).of_norm.hasSum.unique exactSum

theorem seedExponential_contDiff :
    ContDiff ℝ ∞ (seedCoefficientExponential admissible
      (grade := grade) (dimension := dimension)) := by
  have formula : seedCoefficientExponential admissible (grade := grade) (dimension := dimension) =
      operatorExponentialApply (E := Coefficient L sigma gamma ell grade dimension dimension) (leftCompositionOperator admissible grade dimension)
        (gradedIdentityCoefficient L sigma gamma ell grade dimension) :=
    funext (seedExponential_operator_formula admissible grade dimension)
  rw [formula]
  exact operatorExponentialApply_contDiff (E := Coefficient L sigma gamma ell grade dimension dimension) _ _

end Grad.Constraints.Seed
