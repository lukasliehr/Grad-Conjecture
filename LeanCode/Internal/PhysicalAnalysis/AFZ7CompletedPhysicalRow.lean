import AFZ6ActualPhysicalDefectConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

theorem completedNormalTrace_core (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (field : core) :
    completedNormalTrace admissible data grade core (compensatedIntoClosure admissible grade core field) =
      actualCoreTrace admissible data coherent grade field.val :=
  congrArg (fun vector : apGrade L sigma gamma ell 3 (grade + 1) =>
    apHighTrace L sigma gamma ell (grade + 1) (by omega)
      (apMultiplier admissible (normalRowFamily data (grade + 1)) vector))
    (completedReconstruct_core admissible grade core field)

/-- The full completed augmented operator's boundary component is the SAME
physical normal trace appearing in the signed matching law. -/
theorem completedCurrentRows_physicalBoundary (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    (completedCurrentRows admissible data coherent grade core field).snd =
      completedNormalTrace admissible data grade core field := by
  have decode : Continuous (WithLp.ofLp : CapAugmentedAmbient L sigma gamma ell grade →
      CapSourceAmbient L sigma gamma ell grade × APBoundaryGrade L sigma gamma ell 1 (grade + 1)) :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ (CapSourceAmbient L sigma gamma ell grade)
      (APBoundaryGrade L sigma gamma ell 1 (grade + 1))).continuous
  apply isClosed_property (compensatedIntoClosure_denseRange admissible grade core)
    (isClosed_eq ((continuous_snd.comp decode).comp
      (completedCurrentRows admissible data coherent grade core).continuous)
      (completedNormalTrace admissible data grade core).continuous) _ field
  intro source
  exact (congrArg (fun value : CapAugmentedAmbient L sigma gamma ell grade => value.snd)
    (completedCurrentRows_core admissible data coherent grade core source)).trans
      (completedNormalTrace_core admissible data coherent grade core source).symm

/-- No portion of the full physical boundary component is omitted. -/
theorem capAugmentedPhysicalBoundary_norm (grade : ℕ) (field : CapAugmentedAmbient L sigma gamma ell grade) :
    ‖field.snd‖ ≤ ‖field‖ := by
  have identity := WithLp.prod_norm_sq_eq_of_L2 field
  change ‖field‖ ^ 2 = ‖field.fst‖ ^ 2 + ‖field.snd‖ ^ 2 at identity
  nlinarith [sq_nonneg ‖field.fst‖, norm_nonneg field, norm_nonneg field.snd]

/-- Applying R to any high physical leakage preserves its full boundary
norm, and that norm is contained in the unprojected augmented norm. -/
theorem strongAngularLift_physicalBoundary_bound (grade : ℕ)
    (field : CapAugmentedAmbient L sigma gamma ell grade) :
    ‖strongAngularLift L sigma gamma ell grade field.snd‖ ≤ ‖field‖ :=
  (strongAngularLift_norm L sigma gamma ell grade field.snd).trans_le
    ((apHighProjection_bound L sigma gamma ell (grade + 1) field.snd).trans
      (capAugmentedPhysicalBoundary_norm grade field))

end Grad.GaugeCoefficients.Physical.Compensated
