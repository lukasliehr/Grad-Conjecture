import GQD4InverseIdentities

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation

variable {L sigma gamma ell : ℝ} {admissible : Admissible L sigma gamma ell}
  {gauge : CoefficientFamily L sigma gamma ell 3 3}

/-- S-I is compared in the SAME original five-slot ambient graph norm,
since the two constrained closures are different subspaces. -/
def completedTransferDifference (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) (large : 3 ≤ grade) :
    circularCompensatedClosure admissible grade →L[ℂ] CompensatedGraphAmbient L sigma gamma ell grade :=
  (currentCompensatedClosure admissible gauge isomorphism.coherent grade).subtypeL.comp
    (completedTransfer isomorphism grade large) - (circularCompensatedClosure admissible grade).subtypeL

theorem completedTransferDifference_core (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) (large : 3 ≤ grade) (core : circularCompensatedCore admissible) :
    completedTransferDifference isomorphism grade large (compensatedIntoClosure admissible grade _ core) =
      compensatedGraphLinear admissible grade ((isomorphism.equivalence core).val - core.val) :=
  (congrArg (fun point : currentCompensatedClosure admissible gauge isomorphism.coherent grade =>
    point.val - compensatedGraphLinear admissible grade core.val)
      (completedTransfer_core isomorphism grade large core)).trans
        ((compensatedGraphLinear admissible grade).map_sub (isomorphism.equivalence core).val core.val).symm

theorem norm_bound_of_dense_core {C E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (embed : C → E) (dense : DenseRange embed) (mapping : E → F) (continuous : Continuous mapping)
    (constant : ℝ) (coreLaw : ∀ core, ‖mapping (embed core)‖ ≤ constant * ‖embed core‖) (field : E) :
    ‖mapping field‖ ≤ constant * ‖field‖ :=
  isClosed_property dense (isClosed_le continuous.norm (continuous_const.mul continuous_norm)) coreLaw field

theorem completedTransferDifference_pointwise_bound
    (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) (large : 3 ≤ grade) (field : circularCompensatedClosure admissible grade) :
    ‖completedTransferDifference isomorphism grade large field‖ ≤
      (transferPolynomial L sigma gamma grade).eval (gaugeEpsilon (gauge (grade + 3))) * ‖field‖ :=
  norm_bound_of_dense_core (compensatedIntoClosure admissible grade (circularCompensatedCore admissible))
    (compensatedIntoClosure_denseRange admissible grade (circularCompensatedCore admissible))
    (completedTransferDifference isomorphism grade large) (completedTransferDifference isomorphism grade large).continuous
    ((transferPolynomial L sigma gamma grade).eval (gaugeEpsilon (gauge (grade + 3))))
    (fun core => (congrArg norm (completedTransferDifference_core isomorphism grade large core)).trans_le
      (isomorphism.differenceBound grade large core)) field

theorem completedTransferDifference_bound
    (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) (large : 3 ≤ grade) :
    ‖completedTransferDifference isomorphism grade large‖ ≤
      (transferPolynomial L sigma gamma grade).eval (gaugeEpsilon (gauge (grade + 3))) :=
  (completedTransferDifference isomorphism grade large).opNorm_le_bound
    ((transferPolynomial_nonnegative admissible grade).eval_nonnegative (gaugeEpsilon_nonnegative _))
    (completedTransferDifference_pointwise_bound isomorphism grade large)

theorem completedTransfer_unique
    (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) (large : 3 ≤ grade)
    (mapping : circularCompensatedClosure admissible grade →L[ℂ]
      currentCompensatedClosure admissible gauge isomorphism.coherent grade)
    (coreLaw : ∀ core, mapping (compensatedIntoClosure admissible grade _ core) =
      compensatedIntoClosure admissible grade _ (isomorphism.equivalence core)) :
    mapping = completedTransfer isomorphism grade large := by
  apply ContinuousLinearMap.ext
  exact congrFun ((compensatedIntoClosure_denseRange admissible grade (circularCompensatedCore admissible)).equalizer
    mapping.continuous (completedTransfer isomorphism grade large).continuous
    (funext (fun core => (coreLaw core).trans (completedTransfer_core isomorphism grade large core).symm)))

end Grad.GaugeCoefficients.Physical.Compensated
