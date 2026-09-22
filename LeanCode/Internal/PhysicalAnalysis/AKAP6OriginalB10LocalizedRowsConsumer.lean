import AKAP5LocalizedRowsSmall

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000

open MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.CartesianUncompressed
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

/-- One original B10 neighborhood, chosen after a fixed physical cutoff
 but before ell and the state, supplies the actual SAME localized a,c,s
 operators on L2 and H1 with arbitrarily small common norm. Original
 width, all cells, full-current Qa and both original gauges are retained. -/
theorem actualOriginalB10LocalizedRows (parameters : PhaseParameters)
    (L radius primitiveThreshold operatorThreshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius)
    (primitivePositive : 0 < primitiveThreshold) (operatorPositive : 0 < operatorThreshold)
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar)
    (included : tsupport scalar ⊆ openUnitDisk) :
    ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
      ∀ (ell rho alpha delta parameter epsilon : ℝ)
        (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
        |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
        ∀ base : ACore parameters 3,
          physicalBudget parameters base rho epsilon 10 < lowRadius →
          ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
            primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ primitiveThreshold ∧
            ∃ inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation),
              ActualLedgerReduction ledger inverseCoherent ∧
              ActualStartupKernelRealization ledger inverseCoherent ∧
              ∀ row : Fin 3, ∃ regular : FieldH1 →L[ℂ] FieldH1,
                (∀ field, valueInclusion (regular field) =
                  startupLocalizedKernel scalar smooth compact
                    (startupERKernelRow admissible ledger.val ledger.property.1 inverseCoherent row) (valueInclusion field)) ∧
                ‖startupLocalizedKernel scalar smooth compact
                  (startupERKernelRow admissible ledger.val ledger.property.1 inverseCoherent row)‖ < operatorThreshold ∧
                ‖regular‖ < operatorThreshold := by
  have denominatorPositive : 0 < startupCutoffConstant scalar smooth compact * startupEREmbeddingConstant + 1 := by
    have := startupCutoffConstant_positive scalar smooth compact
    have := startupEREmbeddingConstant_positive
    positivity
  obtain ⟨lowRadius, lowPositive, lowOne, supplied⟩ := actualOriginalB10SmallRows parameters L radius primitiveThreshold
    (operatorThreshold / (startupCutoffConstant scalar smooth compact * startupEREmbeddingConstant + 1))
    positive radiusNonnegative primitivePositive (div_pos operatorPositive denominatorPositive)
  refine ⟨lowRadius, lowPositive, lowOne, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low
  obtain ⟨ledger, primitiveMargin, inverseCoherent, reduction, realization, small⟩ := supplied
    ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low
  exact ⟨ledger, primitiveMargin, inverseCoherent, reduction, realization,
    startupActualLocalizedRowsSmall scalar smooth compact included ledger inverseCoherent operatorThreshold operatorPositive small⟩

end Grad.CartesianStartup
