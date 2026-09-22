import AKAY25OriginalB10GenuineSmallRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

variable {L sigma gamma ell : ℝ}

def startupGenuineERKernelRow (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (row : Fin 3) : StartupL2 3 →L[ℂ] StartupL2 3 :=
  ![(originalValueKernel planarInclusionMap).comp (startupGenuineForceKernel admissible data coherent inverseCoherent),
    (originalValueKernel toroidalInclusionMap).comp (originalThirdCorrectionKernel admissible data coherent inverseCoherent),
    (originalValueKernel planarInclusionMap).comp (startupGenuinePrincipalFluxKernel admissible data coherent inverseCoherent)] row

def startupGenuineERFirstRow (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (row : Fin 3) : StartupFirst 3 →L[ℂ] StartupFirst 3 :=
  ![(originalValueFirstGraph planarInclusionMap).comp (startupGenuineForceFirst admissible data coherent inverseCoherent),
    (originalValueFirstGraph toroidalInclusionMap).comp (originalThirdCorrectionFirstGraph admissible data coherent inverseCoherent),
    (originalValueFirstGraph planarInclusionMap).comp (startupGenuinePrincipalFluxFirst admissible data coherent inverseCoherent)] row

theorem startupGenuineERRow_compatible (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (row : Fin 3) : StartupCompatible (startupGenuineERKernelRow admissible data coherent inverseCoherent row)
      (startupGenuineERFirstRow admissible data coherent inverseCoherent row) := by
  fin_cases row
  · exact startupCompatible_comp (originalValueFirstGraph_compatible _) (startupGenuineForce_compatible _ _ _ _)
  · exact startupCompatible_comp (originalValueFirstGraph_compatible _) (originalThirdCorrectionFirstGraph_compatible _ _ _ _)
  · exact startupCompatible_comp (originalValueFirstGraph_compatible _) (startupGenuinePrincipalFlux_compatible _ _ _ _)

theorem startupGenuineERRowsSmall {parameters : PhaseParameters}
    {L ell rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation))
    (threshold : ℝ) (small : ActualGenuineStartupRowsSmall ledger inverseCoherent threshold) :
    ∀ row : Fin 3,
      ‖startupGenuineERKernelRow admissible ledger.val ledger.property.1 inverseCoherent row‖ < startupEREmbeddingConstant * threshold ∧
      ‖startupGenuineERFirstRow admissible ledger.val ledger.property.1 inverseCoherent row‖ < startupEREmbeddingConstant * threshold := by
  have bp : ‖originalValueKernel planarInclusionMap‖ ≤ startupEREmbeddingConstant := by
    unfold startupEREmbeddingConstant
    linarith [norm_nonneg (originalValueFirstGraph planarInclusionMap),
      norm_nonneg (originalValueKernel toroidalInclusionMap), norm_nonneg (originalValueFirstGraph toroidalInclusionMap)]
  have bpf : ‖originalValueFirstGraph planarInclusionMap‖ ≤ startupEREmbeddingConstant := by
    unfold startupEREmbeddingConstant
    linarith [norm_nonneg (originalValueKernel planarInclusionMap),
      norm_nonneg (originalValueKernel toroidalInclusionMap), norm_nonneg (originalValueFirstGraph toroidalInclusionMap)]
  have bt : ‖originalValueKernel toroidalInclusionMap‖ ≤ startupEREmbeddingConstant := by
    unfold startupEREmbeddingConstant
    linarith [norm_nonneg (originalValueKernel planarInclusionMap),
      norm_nonneg (originalValueFirstGraph planarInclusionMap), norm_nonneg (originalValueFirstGraph toroidalInclusionMap)]
  have btf : ‖originalValueFirstGraph toroidalInclusionMap‖ ≤ startupEREmbeddingConstant := by
    unfold startupEREmbeddingConstant
    linarith [norm_nonneg (originalValueKernel planarInclusionMap),
      norm_nonneg (originalValueFirstGraph planarInclusionMap), norm_nonneg (originalValueKernel toroidalInclusionMap)]
  intro row
  fin_cases row
  · exact ⟨startupEmbedding_norm_lt _ _ startupEREmbeddingConstant_positive bp small.1,
      startupEmbedding_norm_lt _ _ startupEREmbeddingConstant_positive bpf small.2.2.2.2.1⟩
  · exact ⟨startupEmbedding_norm_lt _ _ startupEREmbeddingConstant_positive bt small.2.1,
      startupEmbedding_norm_lt _ _ startupEREmbeddingConstant_positive btf small.2.2.2.2.2.1⟩
  · exact ⟨startupEmbedding_norm_lt _ _ startupEREmbeddingConstant_positive bp small.2.2.2.1,
      startupEmbedding_norm_lt _ _ startupEREmbeddingConstant_positive bpf small.2.2.2.2.2.2.2⟩

end Grad.CartesianStartup
