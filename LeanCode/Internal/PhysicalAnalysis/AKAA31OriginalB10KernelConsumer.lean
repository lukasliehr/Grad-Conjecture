import AKAA30ActualCurrentFirstGraphs

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace Grad.CartesianStartup

open Grad.ClosedJets Grad.CartesianState Grad.CartesianUncompressed
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

/-- The exact current and ER11 zero-order factors are realized on both L2
 and the existing genuine first weak graph. The low-order matrix constants
 retain the original phase width and have no inverse power of ell. -/
def ActualStartupKernelRealization {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation)) : Prop :=
  StartupCompatible
      (originalCurrentKernel admissible ledger.val.gaugeDeviation ledger.property.1.2.2.2.1 inverseCoherent)
      (originalCurrentFirstGraph admissible ledger.val.gaugeDeviation ledger.property.1.2.2.2.1 inverseCoherent) ∧
  StartupCompatible (originalForceCorrectionKernel admissible ledger.val ledger.property.1 inverseCoherent)
      (originalForceCorrectionFirstGraph admissible ledger.val ledger.property.1 inverseCoherent) ∧
  StartupCompatible (originalThirdCorrectionKernel admissible ledger.val ledger.property.1 inverseCoherent)
      (originalThirdCorrectionFirstGraph admissible ledger.val ledger.property.1 inverseCoherent) ∧
  StartupCompatible (originalPrincipalFluxKernel admissible ledger.val ledger.property.1 inverseCoherent)
      (originalPrincipalFluxFirstGraph admissible ledger.val ledger.property.1 inverseCoherent) ∧
  (∀ (input output : ℕ) (family : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
      (coherent : FamilyCoherent family),
    ‖originalMatrixKernel admissible family coherent‖ ≤
        startupDerivativeConstant L parameters.sigma0 parameters.gamma zeroDerivativeIndex * ‖family 0‖ ∧
    ‖startupMatrixFirstGraphCLM admissible family coherent‖ ≤ startupMatrixFirstBudget family)

theorem actualStartupKernelRealization {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation)) :
    ActualStartupKernelRealization ledger inverseCoherent :=
  ⟨originalCurrentFirstGraph_compatible _ _ _ _, originalForceCorrectionFirstGraph_compatible _ _ _ _,
    originalThirdCorrectionFirstGraph_compatible _ _ _ _, originalPrincipalFluxFirstGraph_compatible _ _ _ _,
    fun _ _ family coherent => ⟨originalMatrixKernel_bound admissible family coherent,
      startupMatrixFirstGraphCLM_norm admissible family coherent⟩⟩

/-- A fixed B10 neighborhood supplies the actual ledger, the original two
 gauges, the exact smooth-field ER equations and their same L2/first-graph
 kernel realizations. This statement does not assert resolvent contraction
 or H1/H2 regularity of an arbitrary L2 solution. -/
theorem actualOriginalB10KernelRealization (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
      ∀ (ell rho alpha delta parameter epsilon : ℝ)
        (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
        |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
        ∀ base : ACore parameters 3,
          physicalBudget parameters base rho epsilon 10 < lowRadius →
          ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
            primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ threshold ∧
            ∃ inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation),
              ActualLedgerReduction ledger inverseCoherent ∧ ActualStartupKernelRealization ledger inverseCoherent := by
  obtain ⟨lowRadius, positiveRadius, unitRadius, supplied⟩ :=
    actualOriginalB8CartesianReduction parameters L radius threshold positive radiusNonnegative thresholdPositive
  refine ⟨lowRadius, positiveRadius, unitRadius, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low
  have lowEight := (physicalBudget_monotone parameters base rho epsilon (by norm_num : 8 ≤ 10)).trans_lt low
  obtain ⟨ledger, margin, inverseCoherent, reduction⟩ := supplied ell rho alpha delta parameter epsilon admissible
    alphaSmall deltaSmall parameterSmall base lowEight
  exact ⟨ledger, margin, inverseCoherent, reduction, actualStartupKernelRealization ledger inverseCoherent⟩

end Grad.CartesianStartup
