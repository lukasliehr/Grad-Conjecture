import GC11Inverse

noncomputable section

set_option maxHeartbeats 3000000

open Grad.GenericCarriers Grad.ClosedJets Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann

open Grad.GaugeCoefficients.Algebra

theorem coefficientValue_sub {L sigma gamma ell : ℝ} {dimension : ℕ}
    (first second : BaseCoefficient L sigma gamma ell dimension)
    (cell : ℤ) (point : ClosedDisk) :
    coefficientValue (first - second) cell point =
      coefficientValue first cell point - coefficientValue second cell point := by
  unfold coefficientValue
  change ((coefficientScale L sigma gamma ell 0 cell zeroDerivativeIndex point : ℂ)⁻¹) •
      (weightedDerivative first cell zeroDerivativeIndex point -
        weightedDerivative second cell zeroDerivativeIndex point) =
    ((coefficientScale L sigma gamma ell 0 cell zeroDerivativeIndex point : ℂ)⁻¹) •
        weightedDerivative first cell zeroDerivativeIndex point -
      ((coefficientScale L sigma gamma ell 0 cell zeroDerivativeIndex point : ℂ)⁻¹) •
        weightedDerivative second cell zeroDerivativeIndex point
  rw [smul_sub]

theorem fourierEvaluation_sub {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (first second : BaseCoefficient L sigma gamma ell dimension)
    (angle : ℝ) (point : ClosedDisk) :
    fourierEvaluation (first - second) angle point =
      fourierEvaluation first angle point - fourierEvaluation second angle point := by
  change (∑' cell : ℤ, fourierPhase cell angle •
      coefficientValue (first - second) cell point) =
    (∑' cell : ℤ, fourierPhase cell angle • coefficientValue first cell point) -
      ∑' cell : ℤ, fourierPhase cell angle • coefficientValue second cell point
  simp_rw [coefficientValue_sub, smul_sub]
  exact (fourierTerm_summable admissible first angle point).tsum_sub
    (fourierTerm_summable admissible second angle point)

theorem coefficientNeumannInverse_pointwise {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (positive : 0 < dimension)
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (theta : ℝ)
    (normBound : ‖coefficient‖ ≤ theta) (thetaLt : theta < 1)
    (angle : ℝ) (point : ClosedDisk) :
    (ContinuousLinearMap.id ℂ (PhysicalValue dimension) -
        fourierEvaluation coefficient angle point).comp
          (fourierEvaluation (coefficientNeumannInverse admissible coefficient) angle point) =
        ContinuousLinearMap.id ℂ (PhysicalValue dimension) ∧
      (fourierEvaluation (coefficientNeumannInverse admissible coefficient) angle point).comp
          (ContinuousLinearMap.id ℂ (PhysicalValue dimension) -
            fourierEvaluation coefficient angle point) =
        ContinuousLinearMap.id ℂ (PhysicalValue dimension) := by
  constructor
  · have evaluated := congrArg
        (fun value : BaseCoefficient L sigma gamma ell dimension =>
          fourierEvaluation value angle point)
        (coefficientNeumannInverse_left_identity admissible positive coefficient theta
          normBound thetaLt)
    rw [fourierComposition admissible,
      fourierEvaluation_sub admissible,
      identityCoefficient_fourier] at evaluated
    exact evaluated
  · have evaluated := congrArg
        (fun value : BaseCoefficient L sigma gamma ell dimension =>
          fourierEvaluation value angle point)
        (coefficientNeumannInverse_right_identity admissible positive coefficient theta
          normBound thetaLt)
    rw [fourierComposition admissible,
      fourierEvaluation_sub admissible,
      identityCoefficient_fourier] at evaluated
    exact evaluated

end Grad.GaugeCoefficients.Neumann
