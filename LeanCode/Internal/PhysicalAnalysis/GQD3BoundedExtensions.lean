import GQD2ActualClosures

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Allocation

variable {L sigma gamma ell : ℝ} {admissible : Admissible L sigma gamma ell}
  {gauge : CoefficientFamily L sigma gamma ell 3 3}

local instance closureGroup (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    NormedAddCommGroup (compensatedClosure admissible grade core) := inferInstance

local instance closureSeminormed (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    SeminormedAddCommGroup (compensatedClosure admissible grade core) :=
  (closureGroup admissible grade core).toSeminormedAddCommGroup

local instance closureNormedSpace (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    NormedSpace ℂ (compensatedClosure admissible grade core) where
  norm_smul_le scalar field := norm_smul_le scalar field.val

def completedTransferConstant (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) : ℝ :=
  (transferPolynomial L sigma gamma grade).eval (gaugeEpsilon (gauge (grade + 3))) + 1

theorem completedTransferConstant_nonnegative (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) :
    0 ≤ completedTransferConstant gauge grade :=
  add_nonneg ((transferPolynomial_nonnegative admissible grade).eval_nonnegative
    (gaugeEpsilon_nonnegative (gauge (grade + 3)))) zero_le_one

theorem backwardDifferenceConstant_nonnegative (grade : ℕ) : 0 ≤ backwardDifferenceConstant grade :=
  mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) removedGraphConstant_nonnegative)
    (apComplementConstant_nonnegative (grade + 1))) remainderBoundConstant_nonnegative

theorem completedTransfer_exists (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) (large : 3 ≤ grade) :
    ∃ mapping : circularCompensatedClosure admissible grade →L[ℂ]
        currentCompensatedClosure admissible gauge isomorphism.coherent grade,
      (∀ core : circularCompensatedCore admissible,
        mapping (compensatedIntoClosure admissible grade (circularCompensatedCore admissible) core) =
        compensatedIntoClosure admissible grade (currentCompensatedCore admissible gauge isomorphism.coherent)
          (isomorphism.equivalence core)) ∧
      ‖mapping‖ ≤ completedTransferConstant gauge grade := by
  exact coreGraph_extension (C := circularCompensatedCore admissible)
    (E := CompensatedGraphAmbient L sigma gamma ell grade)
    (T := currentCompensatedClosure admissible gauge isomorphism.coherent grade)
    (compensatedCoreGraph admissible grade (circularCompensatedCore admissible))
    ((compensatedIntoClosure admissible grade (currentCompensatedCore admissible gauge isomorphism.coherent)).comp
      isomorphism.equivalence.toLinearMap)
    (completedTransferConstant gauge grade) (completedTransferConstant_nonnegative admissible gauge grade)
    (isomorphism.forwardBound grade large)

def completedTransfer (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) (large : 3 ≤ grade) :
    circularCompensatedClosure admissible grade →L[ℂ]
      currentCompensatedClosure admissible gauge isomorphism.coherent grade :=
  (completedTransfer_exists isomorphism grade large).choose

theorem completedTransfer_core (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) (large : 3 ≤ grade) (core : circularCompensatedCore admissible) :
    completedTransfer isomorphism grade large (compensatedIntoClosure admissible grade _ core) =
      compensatedIntoClosure admissible grade _ (isomorphism.equivalence core) :=
  (completedTransfer_exists isomorphism grade large).choose_spec.1 core

theorem completedTransfer_bound (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) (large : 3 ≤ grade) :
    ‖completedTransfer isomorphism grade large‖ ≤ completedTransferConstant gauge grade :=
  (completedTransfer_exists isomorphism grade large).choose_spec.2

theorem completedInverse_exists (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) :
    ∃ mapping : currentCompensatedClosure admissible gauge isomorphism.coherent grade →L[ℂ]
        circularCompensatedClosure admissible grade,
      (∀ core : currentCompensatedCore admissible gauge isomorphism.coherent,
        mapping (compensatedIntoClosure admissible grade (currentCompensatedCore admissible gauge isomorphism.coherent) core) =
        compensatedIntoClosure admissible grade (circularCompensatedCore admissible) (isomorphism.equivalence.symm core)) ∧
      ‖mapping‖ ≤ backwardDifferenceConstant grade + 1 := by
  exact coreGraph_extension (C := currentCompensatedCore admissible gauge isomorphism.coherent)
    (E := CompensatedGraphAmbient L sigma gamma ell grade)
    (T := circularCompensatedClosure admissible grade)
    (compensatedCoreGraph admissible grade (currentCompensatedCore admissible gauge isomorphism.coherent))
    ((compensatedIntoClosure admissible grade (circularCompensatedCore admissible)).comp
      isomorphism.equivalence.symm.toLinearMap)
    (backwardDifferenceConstant grade + 1) (add_nonneg (backwardDifferenceConstant_nonnegative grade) zero_le_one)
    (isomorphism.backwardBound grade)

def completedInverse (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge) (grade : ℕ) :
    currentCompensatedClosure admissible gauge isomorphism.coherent grade →L[ℂ]
      circularCompensatedClosure admissible grade :=
  (completedInverse_exists isomorphism grade).choose

theorem completedInverse_core (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) (core : currentCompensatedCore admissible gauge isomorphism.coherent) :
    completedInverse isomorphism grade (compensatedIntoClosure admissible grade _ core) =
      compensatedIntoClosure admissible grade _ (isomorphism.equivalence.symm core) :=
  (completedInverse_exists isomorphism grade).choose_spec.1 core

theorem completedInverse_bound (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) : ‖completedInverse isomorphism grade‖ ≤ backwardDifferenceConstant grade + 1 :=
  (completedInverse_exists isomorphism grade).choose_spec.2

end Grad.GaugeCoefficients.Physical.Compensated
