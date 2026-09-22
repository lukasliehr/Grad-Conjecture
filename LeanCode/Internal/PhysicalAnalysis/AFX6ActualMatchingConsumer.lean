import AFX5MatchingAngularFlux

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

/-- Exact endpoint Fourier identity for the completed primitive, with original phase. -/
theorem completedMatchingP_endpoint {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (grade : ℕ) (large : 1 ≤ grade) (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) (mode : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell (grade + 1)
      (completedMatchingP admissible data grade core field) mode =
      fourierCoeff (fun angle : CellCircle =>
        apTrace admissible (by omega) mode.2 (completedMatchingPrimitive admissible data grade core field)
          (boundaryDiskPoint angle)) mode.1 :=
  apBoundaryTrace_literal admissible (by omega) _ mode

theorem completedMatchingP_unique {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data) (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (mapping : compensatedClosure admissible grade core →L[ℂ] APBoundaryGrade L sigma gamma ell 1 (grade + 1))
    (onCore : ∀ field : core,
      mapping (compensatedIntoClosure admissible grade core field) =
        apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
          (apSmoothGrade L sigma gamma ell 1 (grade + 1) (smoothMatchingPrimitive admissible data coherent field.val))) :
    mapping = completedMatchingP admissible data grade core := by
  apply ContinuousLinearMap.ext
  intro field
  apply isClosed_property (compensatedIntoClosure_denseRange admissible grade core)
    (isClosed_eq mapping.continuous (completedMatchingP admissible data grade core).continuous) _ field
  intro source
  exact (onCore source).trans (completedMatchingP_core admissible data coherent grade core source).symm

/-- Actual constructor on the SAME physical low ball as the accepted gauge
transfer. No ledger, transfer or matching trace is assumed as a new input. -/
theorem actualMatchingTraceConsumer (parameters : PhaseParameters) (L radius threshold : ℝ)
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
              ∀ grade (large : 3 ≤ grade),
                let core := currentCompensatedCore admissible ledger.val.gaugeDeviation smooth.coherent
                (∀ source : core,
                  completedMatchingP admissible ledger.val grade core (compensatedIntoClosure admissible grade core source) =
                    apBoundaryTrace L parameters.sigma0 parameters.gamma ell (grade + 1) (by omega)
                      (apSmoothGrade L parameters.sigma0 parameters.gamma ell 1 (grade + 1)
                        (smoothMatchingPrimitive admissible ledger.val ledger.property.1 source.val))) ∧
                (∀ field : compensatedClosure admissible grade core,
                  ‖completedMatchingP admissible ledger.val grade core field‖ ≤ matchingTraceConstant ledger.val grade * ‖field‖ ∧
                  ‖completedMatchingX admissible ledger.val grade core field‖ ≤ matchingTraceConstant ledger.val grade * ‖field‖ ∧
                  ∀ mode : ℤ × ℤ,
                    apBoundaryCoefficient L parameters.sigma0 parameters.gamma ell grade
                      (completedMatchingX admissible ledger.val grade core field) mode =
                      (Complex.I * (mode.1 : ℂ)) •
                        apBoundaryCoefficient L parameters.sigma0 parameters.gamma ell (grade + 1)
                          (completedMatchingP admissible ledger.val grade core field) mode) ∧
                (∀ field : circularCompensatedClosure admissible grade,
                  completedMatchingD admissible grade core (completedTransfer smooth grade large field) =
                    completedMatchingD admissible grade (circularCompensatedCore admissible) field) ∧
                (∀ field : circularCompensatedClosure admissible grade,
                  let output := completedTransfer smooth grade large field
                  completedMatchingP admissible ledger.val grade core output -
                    completedCircleMatchingP admissible grade (circularCompensatedCore admissible) field =
                      apBoundaryTrace L parameters.sigma0 parameters.gamma ell (grade + 1) (by omega)
                        (apMeanFree L parameters.sigma0 parameters.gamma ell 1 (grade + 1)
                          (apRadialContraction admissible (grade + 1)
                            (apMultiplier admissible (ledger.val.fluxDeviation (grade + 1))
                              (completedReconstruct admissible grade core output)) +
                           apTangentContraction admissible (grade + 1)
                             (apMultiplier admissible (ledger.val.fluxDeviation (grade + 1))
                               (apMatchingRadialColumn admissible (grade + 1)
                                 (completedPsi admissible grade (circularCompensatedCore admissible) field)))))) := by
  have result := actualScalarTracePreservation parameters L radius threshold positive radiusNonnegative thresholdPositive
  let lowRadius := result.choose
  have neighborhood := result.choose_spec
  refine ⟨lowRadius, neighborhood.1, neighborhood.2.1, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low bounded
  have supplied := neighborhood.2.2 ell rho alpha delta parameter epsilon admissible
    alphaSmall deltaSmall parameterSmall base low bounded
  let ledger := supplied.choose
  have state := supplied.choose_spec
  let smooth := state.2.choose
  refine ⟨ledger, state.1, smooth, state.2.choose_spec.1, ?_⟩
  intro grade large
  dsimp only
  refine ⟨fun source => completedMatchingP_core admissible ledger.val ledger.property.1 grade _ source,
    fun field => ⟨completedMatchingP_bound admissible ledger.val grade _ field,
      completedMatchingX_bound admissible ledger.val grade _ field,
      fun mode => completedMatchingX_coefficient admissible ledger.val grade (by omega) _ field mode⟩,
    fun field => completedMatchingD_transfer admissible smooth grade large field,
    fun field => completedMatchingP_difference admissible ledger.val smooth grade large field⟩

end Grad.GaugeCoefficients.Physical.Compensated

