import GQF3ComparisonInterface

noncomputable section
set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

/-- Interface-only universal application check. This does not construct the
record or claim the public comparison theorem. The final consumer will obtain
the record from the proved actual-state constructor. -/
theorem checked_forward_comparison_application {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation)
    (grade : ℕ) (large : 3 ≤ grade)
    (construction : CompletedForwardComparison admissible data coherent smooth grade large)
    (field : circularCompensatedClosure admissible grade) :
    construction.current (completedTransfer smooth grade large field) - construction.circle field =
      construction.error
        (Grad.GaugeCoefficients.Physical.GaugeTransfer.apCurrentProjection admissible data.gaugeDeviation (grade + 1)
          (completedReconstruct admissible grade (circularCompensatedCore admissible) field)) :=
  construction.difference field

#check Grad.GaugeCoefficients.Physical.RadialLedger.apComplement
#check Grad.GaugeCoefficients.Physical.RadialLedger.apFiniteInto_denseRange
#check Grad.GaugeCoefficients.Physical.RadialLedger.apL2Trace_ext
#check Grad.GaugeCoefficients.Physical.RadialLedger.apClosedJet_weak
#check Grad.GaugeCoefficients.Physical.GaugeTransfer.rotationJet_fixedComplement
#check Grad.GaugeCoefficients.Physical.GaugeTransfer.actualComplementAngularAction
#check Grad.GaugeCoefficients.Physical.Compensated.apPartial_bound
#check Grad.GaugeCoefficients.Physical.Compensated.apAxial_bound
#check Grad.GaugeCoefficients.Physical.RadialLedger.apMultiplier_bound
#check Grad.GaugeCoefficients.Physical.Compensated.compensatedIntoClosure_denseRange
#check Grad.GaugeCoefficients.Physical.Compensated.completedReconstruct_transfer
#check Grad.GaugeCoefficients.Physical.Compensated.completedNormalTrace_difference_Qa
#check Grad.GaugeCoefficients.Physical.Compensated.actualNormalRow_matrix
#check Grad.GaugeCoefficients.Physical.Compensated.actualScalarTracePreservation
#check Grad.GaugeCoefficients.Physical.Ledger.actualLedger

#print Grad.GaugeCoefficients.Physical.Compensated.ActualForwardComparisonGoal
#print Grad.GaugeCoefficients.Physical.Compensated.CompletedForwardComparison
#print Grad.GaugeCoefficients.Physical.Compensated.ComplementCancellationGoal
#print Grad.GaugeCoefficients.Physical.Compensated.SmoothForwardComparison
#print Grad.GaugeCoefficients.Physical.Compensated.CapSourceAmbient
#print Grad.GaugeCoefficients.Physical.Compensated.CapAugmentedAmbient
#print Grad.GaugeCoefficients.Physical.Compensated.smoothCapSourceCore
#print Grad.GaugeCoefficients.Physical.Compensated.capSourceClosure

end Grad.GaugeCoefficients.Physical.Compensated
