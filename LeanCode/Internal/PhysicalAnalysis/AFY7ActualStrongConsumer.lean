import AFY6StrongTransfer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace

theorem strongMatchingTarget_complete (L sigma gamma ell : ℝ) (grade : ℕ) :
    CompleteSpace (StrongMatchingPair L sigma gamma ell grade) := inferInstance

/-- All exact completed matching laws, proved before specializing to the
physical low-ball witness. This keeps its witness proof from expanding the
native lp and graph representations during elaboration. -/
def StrongMatchingLaws {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation) : Prop :=
∀ grade (large : 3 ≤ grade),
  let core := currentCompensatedCore admissible data.gaugeDeviation smooth.coherent
  (∀ field : compensatedClosure admissible grade core,
    strongMatchingWeak L sigma gamma ell (grade + 1)
        (completedStrongScalar admissible grade core field) =
      (ell : ℂ)⁻¹ • apHighProjection L sigma gamma ell (grade + 1)
        (completedMatchingD admissible grade core field) ∧
    strongMatchingWeak L sigma gamma ell grade
        (completedStrongFlux admissible data grade core field) =
      apHighProjection L sigma gamma ell grade
        (completedMatchingX admissible data grade core field) ∧
    ‖completedStrongPair admissible data grade core field‖ =
      ‖apHighProjection L sigma gamma ell (grade + 2)
        (completedNativeThetaTrace admissible grade core field)‖ +
      ‖apHighProjection L sigma gamma ell (grade + 1)
        (completedMatchingP admissible data grade core field)‖ ∧
    ‖completedStrongPair admissible data grade core field‖ ≤
      (Real.sqrt (traceCellConstant (grade + 2)) + matchingTraceConstant data grade) * ‖field‖) ∧
  (∀ source : core, ∀ mode : ℤ × ℤ,
    strongMatchingCoefficient L sigma gamma ell grade
        (completedStrongFlux admissible data grade core
          (compensatedIntoClosure admissible grade core source)) mode =
      if 3 ≤ |mode.1| then
        fourierCoeff (fun angle : CellCircle =>
          (apSmoothJet admissible 1 mode.2
            (apSmoothRotation admissible 1
              (smoothMatchingPrimitive admissible data coherent source.val))).value
                (boundaryDiskPoint angle)) mode.1
      else 0) ∧
  (∀ field : circularCompensatedClosure admissible grade,
    completedStrongScalar admissible grade core (completedTransfer smooth grade large field) =
      completedStrongScalar admissible grade (circularCompensatedCore admissible) field)

theorem strongMatchingCompletedLaws {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation) :
    StrongMatchingLaws admissible data coherent smooth := by
  intro grade large
  let core := currentCompensatedCore admissible data.gaugeDeviation smooth.coherent
  refine ⟨?_, ?_, ?_⟩
  · intro field
    exact ⟨completedStrongScalar_weak admissible grade (by omega) core field,
      completedStrongFlux_weak admissible data grade core field,
      completedStrongPair_norm admissible data grade core field,
      completedStrongPair_bound admissible data grade core field⟩
  · intro source mode
    exact completedStrongFlux_core admissible data coherent grade (by omega) core source mode
  · intro field
    exact completedStrongScalar_transfer smooth grade large field


/-- The actual one-low-ball constructor into AY's stronger matching space.
The same ledger and genuine gauge transfer come from the accepted physical
construction. Bounds here use the explicit native coefficient constants. -/
theorem actualStrongMatchingConsumer (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
      ∀ (ell rho alpha delta parameter epsilon : ℝ)
        (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
        |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
        ∀ base : ACore parameters 3,
          physicalBudget parameters base rho epsilon 10 < lowRadius →
          physicalBudget parameters base rho epsilon 12 ≤ 1 →
          ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
            primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ threshold ∧
            ∃ smooth : SmoothCompensatedCoreIsomorphism admissible ledger.val.gaugeDeviation,
              ScalarTracePreservation admissible ledger.val smooth ∧
              StrongMatchingLaws admissible ledger.val ledger.property.1 smooth := by
  have result := actualScalarTracePreservation parameters L radius threshold positive radiusNonnegative thresholdPositive
  let lowRadius := result.choose
  have neighborhood := result.choose_spec
  refine ⟨lowRadius, neighborhood.1, neighborhood.2.1, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaBound deltaBound parameterBound base small bounded
  obtain ⟨ledger, primitive, smooth, preservation⟩ :=
    neighborhood.2.2 ell rho alpha delta parameter epsilon admissible alphaBound deltaBound parameterBound base small bounded
  exact ⟨ledger, primitive, smooth, preservation.1,
    strongMatchingCompletedLaws (L := L) (sigma := parameters.sigma0)
      (gamma := parameters.gamma) (ell := ell) admissible ledger.val ledger.property.1 smooth⟩

end Grad.GaugeCoefficients.Physical.Compensated
