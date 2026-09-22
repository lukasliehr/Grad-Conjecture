import AKDX9CanonicalPolarTensorEnergy
import AKDY4ActualEulerRadialEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace Grad.OriginalCollarNorm
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift
open Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.SourceCollarCoefficients
open Grad.AnnularGeneralSourceRegularity Grad.OriginalRadialRecovery Grad.OriginalCartesianTameEstimate

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℝ)
  (positive : 0<lower) (bounded : lower<1) (core : ACore parameters dimension)

/-- Stored raw Hilbert jets are the actual ordinary derivatives of the
SAME canonical weighted curve, including both closed-collar endpoints. -/
theorem canonicalRadialJet_fidelity (power rank : ℕ) :
    EqOn (iteratedDerivWithin rank
      (cartesianWeightedRadialCurve parameters lower positive bounded core power 0) (Icc lower 1))
      (cartesianWeightedRadialCurve parameters lower positive bounded core power rank) (Icc lower 1) := by
  induction rank with
  | zero => intro radius _; rfl
  | succ rank previous =>
      intro radius inside
      rw [iteratedDerivWithin_succ,derivWithin_congr previous (previous inside)]
      exact (cartesianWeightedRadialCurve_derivative parameters lower positive bounded core power rank radius inside).derivWithin
        (uniqueDiffOn_Icc bounded radius inside)

/-- A finite set of actual Euler energies pays one canonical raw radial
jet in the full Fourier Hilbert norm before any axial-cell sum is taken. -/
theorem canonicalRadialJet_squareEnergy (power rank : ℕ) (payment : ℝ) (paymentNonnegative : 0≤payment)
    (energy : ∀ order,order≤rank →
      (∫⁻ radius in Icc lower 1,ENNReal.ofReal
        (‖vectorEulerWithinIteratedDerivative (Icc lower 1) order
          (cartesianWeightedRadialCurve parameters lower positive bounded core power 0) radius‖^2))≤ENNReal.ofReal (payment^2)) :
    (∫⁻ radius in Icc lower 1,ENNReal.ofReal
      (‖cartesianWeightedRadialCurve parameters lower positive bounded core power rank radius‖^2))≤
      ENNReal.ofReal ((rawRadialEnergyConstant lower rank*payment)^2) := by
  have paid := actualEuler_radial_squareEnergy lower positive bounded
    (cartesianWeightedRadialCurve parameters lower positive bounded core power 0)
    (cartesianWeightedRadialCurve_smooth parameters lower positive bounded core power 0)
    rank payment paymentNonnegative energy
  have identity :
      (∫⁻ radius in Icc lower 1,ENNReal.ofReal
        (‖cartesianWeightedRadialCurve parameters lower positive bounded core power rank radius‖^2))=
      ∫⁻ radius in Icc lower 1,ENNReal.ofReal
        (‖iteratedDerivWithin rank (cartesianWeightedRadialCurve parameters lower positive bounded core power 0)
          (Icc lower 1) radius‖^2) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
    rw [canonicalRadialJet_fidelity parameters lower positive bounded core power rank inside]
  exact identity.trans_le paid

/-- The identical canonical raw energy as an ordinary radial integral. -/
theorem canonicalRadialJet_integral (power rank : ℕ) (payment : ℝ) (paymentNonnegative : 0≤payment)
    (energy : ∀ order,order≤rank →
      (∫⁻ radius in Icc lower 1,ENNReal.ofReal
        (‖vectorEulerWithinIteratedDerivative (Icc lower 1) order
          (cartesianWeightedRadialCurve parameters lower positive bounded core power 0) radius‖^2))≤ENNReal.ofReal (payment^2)) :
    (∫ radius in lower..1,‖cartesianWeightedRadialCurve parameters lower positive bounded core power rank radius‖^2)≤
      (rawRadialEnergyConstant lower rank*payment)^2 := by
  have paid := canonicalRadialJet_squareEnergy parameters lower positive bounded core power rank payment paymentNonnegative energy
  have integrable : IntegrableOn (fun radius =>
      ‖cartesianWeightedRadialCurve parameters lower positive bounded core power rank radius‖^2) (Icc lower 1) volume :=
    ((cartesianWeightedRadialCurve_continuous parameters lower positive bounded core power rank).norm.pow 2).continuousOn.integrableOn_Icc
  rw [←ofReal_integral_eq_lintegral_ofReal integrable (Eventually.of_forall (fun _ => sq_nonneg _))] at paid
  have realPaid := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg (rawRadialEnergyConstant lower rank*payment))).mp paid
  simpa only [intervalIntegral.integral_of_le bounded.le,←integral_Icc_eq_integral_Ioc] using realPaid

end Grad.OriginalCollarNorm
