import GC18CoefficientBounds

noncomputable section

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

theorem actualGaugeDeviation_bound {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {field : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon field) (grade : ℕ) :
    ‖ledger.val.gaugeDeviation grade‖ ≤ ledgerSizeFour ledger grade := by
  unfold ledgerSizeFour
  have first := norm_nonneg (ledger.val.inverseTransposeDeviation grade)
  have second := norm_nonneg (ledger.val.seedInverse grade -
    identityFamily L parameters.sigma0 parameters.gamma ell 2 grade)
  have third := norm_nonneg (ledger.val.fluxDeviation grade)
  have fourth := norm_nonneg (ledger.val.traceDeviation grade)
  dsimp only [identityFamily] at second
  linarith

/-- Immediate actual-GC17 consumer. The four constructed IΔΠ/Π families
obey AQ16 on one fixed low neighborhood, simultaneously at every grade. -/
theorem actualRadialNumeratorLedger (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
      ∃ muBounds etaBounds nuBounds deltaBounds : ℕ → ℝ,
        (∀ grade, 0 ≤ muBounds grade ∧ 0 ≤ etaBounds grade ∧ 0 ≤ nuBounds grade ∧ 0 ≤ deltaBounds grade) ∧
        ∀ (ell rho alpha delta parameter epsilon : ℝ)
          (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
          |rho| ≤ 1 → |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius → |epsilon| ≤ 1 →
          ∀ field : ACore parameters 3, physicalBudget parameters field rho epsilon 6 ≤ lowRadius →
            ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon field,
              primitiveSize parameters admissible rho alpha delta parameter epsilon field 2 ≤ threshold ∧
              ∀ grade,
                ‖muDeviation admissible ledger.val.gaugeDeviation grade‖ ≤ muBounds grade * physicalBudget parameters field rho epsilon (grade + 6) ∧
                ‖etaCoefficient admissible ledger.val.gaugeDeviation grade‖ ≤ etaBounds grade * physicalBudget parameters field rho epsilon (grade + 6) ∧
                ‖nuCoefficient admissible ledger.val.gaugeDeviation grade‖ ≤ nuBounds grade * physicalBudget parameters field rho epsilon (grade + 6) ∧
                ‖deltaDeviation admissible ledger.val.gaugeDeviation grade‖ ≤ deltaBounds grade * physicalBudget parameters field rho epsilon (grade + 6) := by
  obtain ⟨lowRadius, lowPositive, lowOne, constants, higherConstants, constantsNonnegative, _, supplied⟩ :=
    actualLedger parameters L radius threshold positive radiusNonnegative thresholdPositive
  refine ⟨lowRadius, lowPositive, lowOne, muConstant constants, etaConstant constants,
    nuConstant constants, deltaConstant constants, ?_, ?_⟩
  · intro grade
    exact ⟨muConstant_nonnegative constantsNonnegative grade, etaConstant_nonnegative constantsNonnegative grade,
      nuConstant_nonnegative constantsNonnegative grade, deltaConstant_nonnegative constantsNonnegative grade⟩
  · intro ell rho alpha delta parameter epsilon admissible rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall field low
    obtain ⟨ledger, margin, bounds⟩ := supplied ell rho alpha delta parameter epsilon admissible
      rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall field low
    have gaugeBound (grade : ℕ) : ‖ledger.val.gaugeDeviation grade‖ ≤
        constants grade * physicalBudget parameters field rho epsilon (grade + 4) :=
      (actualGaugeDeviation_bound ledger grade).trans (bounds grade).1
    refine ⟨ledger, margin, fun grade => ?_⟩
    exact ⟨muDeviation_bound parameters admissible field rho epsilon _ constants gaugeBound grade,
      etaCoefficient_bound parameters admissible field rho epsilon _ constants gaugeBound grade,
      nuCoefficient_bound parameters admissible field rho epsilon _ constants gaugeBound grade,
      deltaDeviation_bound parameters admissible field rho epsilon _ constants constantsNonnegative gaugeBound grade⟩

end Grad.GaugeCoefficients.Physical.RadialLedger
