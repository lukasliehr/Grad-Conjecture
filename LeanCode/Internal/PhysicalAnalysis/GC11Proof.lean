import GC11Pointwise

noncomputable section

open Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann

open Grad.GaugeCoefficients.Algebra

def analyticCapCoefficientNeumannInverse {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (coefficient : BaseCoefficient L sigma gamma ell dimension) :
    BaseCoefficient L sigma gamma ell dimension :=
  coefficientNeumannInverse admissible coefficient

theorem analyticCapCoefficientNeumannInverse_baseBound
    {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (positive : 0 < dimension)
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (theta : ℝ)
    (normBound : ‖coefficient‖ ≤ theta) (thetaLt : theta < 1) :
    ‖analyticCapCoefficientNeumannInverse admissible coefficient‖ ≤
      (1 - theta)⁻¹ :=
  coefficientNeumannInverse_norm_le admissible positive coefficient theta normBound thetaLt

theorem analyticCapCoefficientNeumannInverse_twoSidedIdentities
    {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (positive : 0 < dimension)
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (theta : ℝ)
    (normBound : ‖coefficient‖ ≤ theta) (thetaLt : theta < 1) :
    coefficientComposition admissible 0
        (identityCoefficient L sigma gamma ell dimension - coefficient)
        (analyticCapCoefficientNeumannInverse admissible coefficient) =
      identityCoefficient L sigma gamma ell dimension ∧
    coefficientComposition admissible 0
        (analyticCapCoefficientNeumannInverse admissible coefficient)
        (identityCoefficient L sigma gamma ell dimension - coefficient) =
      identityCoefficient L sigma gamma ell dimension :=
  ⟨coefficientNeumannInverse_left_identity admissible positive coefficient theta
      normBound thetaLt,
    coefficientNeumannInverse_right_identity admissible positive coefficient theta
      normBound thetaLt⟩

theorem analyticCapCoefficientNeumannInverse_pointwiseIdentification
    {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (positive : 0 < dimension)
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (theta : ℝ)
    (normBound : ‖coefficient‖ ≤ theta) (thetaLt : theta < 1)
    (angle : ℝ) (point : Grad.ClosedJets.ClosedDisk) :
    (ContinuousLinearMap.id ℂ (Grad.GenericCarriers.PhysicalValue dimension) -
        fourierEvaluation coefficient angle point).comp
          (fourierEvaluation
            (analyticCapCoefficientNeumannInverse admissible coefficient) angle point) =
        ContinuousLinearMap.id ℂ (Grad.GenericCarriers.PhysicalValue dimension) ∧
      (fourierEvaluation
        (analyticCapCoefficientNeumannInverse admissible coefficient) angle point).comp
          (ContinuousLinearMap.id ℂ (Grad.GenericCarriers.PhysicalValue dimension) -
            fourierEvaluation coefficient angle point) =
        ContinuousLinearMap.id ℂ (Grad.GenericCarriers.PhysicalValue dimension) :=
  coefficientNeumannInverse_pointwise admissible positive coefficient theta
    normBound thetaLt angle point

def inverseWitness {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (positive : 0 < dimension)
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (theta : ℝ)
    (normBound : ‖coefficient‖ ≤ theta) (thetaLt : theta < 1) :
    InverseWitness admissible coefficient theta where
  inverse := analyticCapCoefficientNeumannInverse admissible coefficient
  powers_summable := coefficientPower_summable admissible positive coefficient theta
    normBound thetaLt
  series := rfl
  left_inverse := coefficientNeumannInverse_left_identity admissible positive coefficient theta
    normBound thetaLt
  right_inverse := coefficientNeumannInverse_right_identity admissible positive coefficient theta
    normBound thetaLt
  base_norm := analyticCapCoefficientNeumannInverse_baseBound admissible positive coefficient theta
    normBound thetaLt
  pointwise_inverse := analyticCapCoefficientNeumannInverse_pointwiseIdentification
    admissible positive coefficient theta normBound thetaLt

theorem blockGoal : BlockGoal := by
  intro L sigma gamma ell admissible dimension positive coefficient theta normBound thetaLt
  exact ⟨inverseWitness admissible positive coefficient theta normBound thetaLt⟩

end Grad.GaugeCoefficients.Neumann
