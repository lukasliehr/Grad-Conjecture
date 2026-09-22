import GQE13PairedConsumer

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace

/-- Full AO23–25 on the actual smooth cores and their specified AN8
closures. Every map in this interface is the constructed literal map. -/
structure ScalarTracePreservation {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation) where
  smoothPsi : ∀ core : circularCompensatedCore admissible,
    physicalPsi admissible (smooth.equivalence core).val = physicalPsi admissible core.val
  smoothScalar : ∀ core : circularCompensatedCore admissible,
    physicalScalar admissible (smooth.equivalence core).val = physicalScalar admissible core.val
  smoothRadial : ∀ core : circularCompensatedCore admissible,
    physicalRadial admissible (smooth.equivalence core).val = physicalRadial admissible core.val
  psi : ∀ grade (large : 3 ≤ grade) (field : circularCompensatedClosure admissible grade),
    completedPsi admissible grade (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
      (completedTransfer smooth grade large field) = completedPsi admissible grade (circularCompensatedCore admissible) field
  scalar : ∀ grade (large : 3 ≤ grade) (field : circularCompensatedClosure admissible grade),
    completedScalar admissible grade (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
      (completedTransfer smooth grade large field) = completedScalar admissible grade (circularCompensatedCore admissible) field
  radial : ∀ grade (large : 3 ≤ grade) (field : circularCompensatedClosure admissible grade),
    completedRadial admissible grade (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
      (completedTransfer smooth grade large field) = completedRadial admissible grade (circularCompensatedCore admissible) field
  normalDifference : ∀ grade (large : 3 ≤ grade) (field : circularCompensatedClosure admissible grade),
    completedNormalTrace admissible data grade (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
        (completedTransfer smooth grade large field) -
      completedReferenceTrace admissible grade (circularCompensatedCore admissible) field =
      apHighTrace L sigma gamma ell (grade + 1) (by omega)
        (apMultiplier admissible
          (normalRowFamily data (grade + 1) - referenceRowFamily L sigma gamma ell (grade + 1))
          (Grad.GaugeCoefficients.Physical.GaugeTransfer.apCurrentProjection admissible data.gaugeDeviation (grade + 1)
            (completedReconstruct admissible grade (circularCompensatedCore admissible) field)))
  normalBound : ∀ grade (large : 3 ≤ grade) (field : circularCompensatedClosure admissible grade),
    ‖completedNormalTrace admissible data grade (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
        (completedTransfer smooth grade large field) -
      completedReferenceTrace admissible grade (circularCompensatedCore admissible) field‖ ≤
      (Real.sqrt (traceCellConstant (grade + 1)) * apMultiplierConstant L sigma gamma (grade + 1)) *
        ‖data.traceDeviation (grade + 1)‖ *
          ‖completedReconstruct admissible grade (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
            (completedTransfer smooth grade large field)‖

theorem scalarTracePreservation {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation) : ScalarTracePreservation admissible data smooth where
  smoothPsi := transfer_physicalPsi smooth
  smoothScalar := transfer_physicalScalar smooth
  smoothRadial := transfer_physicalRadial smooth
  psi := completedPsi_transfer smooth
  scalar := completedScalar_transfer smooth
  radial := completedRadial_transfer smooth
  normalDifference := completedNormalTrace_difference_Qa admissible data smooth
  normalBound := completedNormalTrace_difference_bound admissible data smooth

end Grad.GaugeCoefficients.Physical.Compensated
