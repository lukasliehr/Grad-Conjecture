import GQC68ActualLedgerIsomorphism

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- Each coordinate in epsilon_q is the original phase/moment weight
times the corresponding literal block of the genuine Cartesian derivative
of the reconstructed actual gauge coefficient. This includes every cell. -/
theorem gaugeBlock_actual_derivative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    {input output : ℕ} (outer : OperatorValue 3 output) (inner : OperatorValue input 3)
    (grade : ℕ) (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    operatorBlockMap outer inner (weightedDerivative (gauge grade) cell index) point =
      (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
        ((outer.comp (smoothOperatorDerivative (actualCoefficientJet admissible gauge coherent cell)
          (derivativeMultiIndex index) point)).comp inner) :=
  (operatorBlockMap_weighted_literal (gauge grade) outer inner cell index point).trans
    (congrArg (fun value : OperatorValue 3 3 =>
      (coefficientScale L sigma gamma ell grade cell index point : ℂ) • ((outer.comp value).comp inner))
      (actualCoefficientJet_coherent admissible gauge coherent cell index point).symm)

/-- The public polynomial retains positivity, zero constant term and
linear control on [0,1], with constants independent of ell and the base. -/
theorem transferPolynomial_contract {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    NonnegativeCoefficients (transferPolynomial L sigma gamma grade) ∧
      (transferPolynomial L sigma gamma grade).eval 0 = 0 ∧
      0 ≤ transferLinearConstant L sigma gamma grade ∧
      ∀ value, 0 ≤ value → value ≤ 1 →
        (transferPolynomial L sigma gamma grade).eval value ≤ transferLinearConstant L sigma gamma grade * value :=
  ⟨transferPolynomial_nonnegative admissible grade, transferPolynomial_zero L sigma gamma grade,
    transferLinearConstant_nonnegative admissible grade, fun _ => transferPolynomial_linear admissible grade⟩

theorem actualCompensatedCoreConsumer (parameters : Grad.CartesianState.PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ActualCompensatedCoreGoal parameters L radius threshold :=
  actualCompensatedCore parameters L radius threshold positive radiusNonnegative thresholdPositive

end Grad.GaugeCoefficients.Physical.Compensated
