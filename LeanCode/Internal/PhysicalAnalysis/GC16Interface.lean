import GC15Consumer
import GC12Proof

noncomputable section

namespace Grad.GaugeCoefficients.Physical.InverseAllocation

open Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation

/-- The actual accepted all-grade Neumann construction, not an assumed inverse. -/
def inverseFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (coefficient : CoefficientFamily L sigma gamma ell dimension dimension) :
    CoefficientFamily L sigma gamma ell dimension dimension :=
  fun grade => gradedCoefficientNeumannInverse admissible (coefficient grade)

/-- AQ11–AQ12 on precisely the existing base ball. Constants precede ell,
the original all-grade physical state and every coefficient value.
The low radius and theta do not change with the output grade. -/
def OneHighInverseGoal : Prop :=
  ∀ (offset grade : ℕ) (lowBound theta : ℝ), 0 ≤ lowBound → theta < 1 →
    ∀ constants : ℕ → ℝ, (∀ order, 0 ≤ constants order) →
      ∃ constant : ℝ, 0 ≤ constant ∧
        ∀ (parameters : PhaseParameters) (L ell : ℝ)
          (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
          (dimension : ℕ), 0 < dimension →
          ∀ (field : ACore parameters 3) (rho epsilon : ℝ)
            (coefficient : CoefficientFamily L parameters.sigma0 parameters.gamma ell dimension dimension),
            FamilyCoherent coefficient →
            physicalBudget parameters field rho epsilon offset ≤ lowBound →
            (∀ order, ‖coefficient order‖ ≤
              constants order * physicalBudget parameters field rho epsilon (offset + order)) →
            ‖coefficient 0‖ ≤ theta →
            ‖analyticCapCoefficientNeumannInverse admissible (coefficient 0)‖ ≤ (1 - theta)⁻¹ ∧
            RealizesSameCoefficient
              (analyticCapCoefficientNeumannInverse admissible (coefficient 0))
              (inverseFamily admissible coefficient grade) ∧
            ‖inverseFamily admissible coefficient grade -
                gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade dimension‖ ≤
              constant * physicalBudget parameters field rho epsilon (offset + grade)

end Grad.GaugeCoefficients.Physical.InverseAllocation
