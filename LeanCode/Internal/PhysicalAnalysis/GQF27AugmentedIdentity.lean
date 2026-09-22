import GQF26CircularBounds
import GQF23ActualSmoothConsumer

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable {L sigma gamma ell : ℝ}

theorem hilbertPairLinear_sub {E F G : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (first second : E →ₗ[ℂ] F) (third fourth : E →ₗ[ℂ] G) (value : E) :
    hilbertPairLinear first third value - hilbertPairLinear second fourth value =
      WithLp.toLp 2 (first value - second value, third value - fourth value) := rfl

theorem actualCoreTrace_difference (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) (grade : ℕ)
    (state : CompensatedData L sigma gamma ell) :
    actualCoreTrace admissible data coherent grade state - circularCoreTrace admissible grade state =
      errorCoreTrace admissible data grade (compensatedReconstruct admissible state) := by
  let vector := apSmoothGrade L sigma gamma ell 3 (grade + 1) (compensatedReconstruct admissible state)
  let trace := apHighTrace (dimension := 1) L sigma gamma ell (grade + 1) (by omega)
  exact linear_trace_difference trace.toLinearMap
    (apRadialContraction admissible (grade + 1) vector) (apRadialContraction admissible (grade + 1) vector)
    (apMultiplier admissible (normalRowFamily data (grade + 1)) vector)
    (apMultiplier admissible (data.traceDeviation (grade + 1)) vector)
    (congrArg (fun mapping : apGrade L sigma gamma ell 3 (grade + 1) →L[ℂ]
      apGrade L sigma gamma ell 1 (grade + 1) => mapping vector)
      (apMultiplier_add admissible (referenceRowFamily L sigma gamma ell (grade + 1))
        (data.traceDeviation (grade + 1)))) rfl

theorem actualAugmentedCore_difference (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) (grade : ℕ)
    (state : CompensatedData L sigma gamma ell) :
    actualAugmentedCore admissible data coherent grade state - circularAugmentedCore admissible grade state =
      errorAugmentedCore admissible data coherent grade (compensatedReconstruct admissible state) := by
  exact congrArg (WithLp.toLp 2) (Prod.ext
    (((capSourceGrade grade).map_sub _ _).symm.trans
      (congrArg (capSourceGrade grade) (actualRows_difference admissible data coherent state)))
    (actualCoreTrace_difference admissible data coherent grade state))

theorem completedReferenceTrace_core (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (state : core) :
    completedReferenceTrace admissible grade core (compensatedIntoClosure admissible grade core state) =
      circularCoreTrace admissible grade state.val := by
  exact congrArg (apHighTrace L sigma gamma ell (grade + 1) (by omega))
    (completedRadial_core admissible grade core state)

theorem circularCoreTrace_transfer (admissible : Admissible L sigma gamma ell)
    {gauge : Grad.GaugeCoefficients.Physical.Allocation.CoefficientFamily L sigma gamma ell 3 3}
    (smooth : SmoothCompensatedCoreIsomorphism admissible gauge) (grade : ℕ) (large : 3 ≤ grade)
    (state : circularCompensatedCore admissible) :
    circularCoreTrace admissible grade (smooth.equivalence state).val = circularCoreTrace admissible grade state.val := by
  have inner := (congrArg (completedRadial admissible grade (currentCompensatedCore admissible gauge smooth.coherent))
    (completedTransfer_core smooth grade large state)).trans
      (completedRadial_core admissible grade (currentCompensatedCore admissible gauge smooth.coherent)
        (smooth.equivalence state))
  have preservation := completedRadial_transfer smooth grade large
    (compensatedIntoClosure admissible grade (circularCompensatedCore admissible) state)
  exact congrArg (apHighTrace L sigma gamma ell (grade + 1) (by omega))
    (inner.symm.trans (preservation.trans (completedRadial_core admissible grade
      (circularCompensatedCore admissible) state)))

theorem circularAugmentedCore_transfer (admissible : Admissible L sigma gamma ell)
    {gauge : Grad.GaugeCoefficients.Physical.Allocation.CoefficientFamily L sigma gamma ell 3 3}
    (smooth : SmoothCompensatedCoreIsomorphism admissible gauge) (grade : ℕ) (large : 3 ≤ grade)
    (state : circularCompensatedCore admissible) :
    circularAugmentedCore admissible grade (smooth.equivalence state).val =
      circularAugmentedCore admissible grade state.val := by
  exact congrArg (WithLp.toLp 2) (Prod.ext
    (congrArg (capSourceGrade grade) (circularRows_transfer admissible smooth state))
    (circularCoreTrace_transfer admissible smooth grade large state))

end Grad.GaugeCoefficients.Physical.Compensated
