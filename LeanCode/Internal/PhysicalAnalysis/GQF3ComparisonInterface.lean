import GQF2SourceCarriers

noncomputable section
set_option maxHeartbeats 1000000
open scoped ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.WeightedTrace

variable {L sigma gamma ell : ℝ}

/-- Full-disk weak planar divergence, defined on the faithful unweighted
L2 realization of each original AP2 cell. No first derivative is a premise. -/
def APPlanarDivergenceZero (grade : ℕ) (field : apGrade L sigma gamma ell 3 grade) : Prop :=
  ∀ (cell : ℤ) (test : Grad.PDEBootstrap.Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test),
      tsupport test ⊆ openUnitDisk →
      apDiskDerivativePairing 3 0 (operatorBasis 0) test smooth compact 1 (fun _ => 0)
          (apL2Trace L sigma gamma ell cell field) +
        apDiskDerivativePairing 3 0 (operatorBasis 1) test smooth compact 1 (fun _ => 1)
          (apL2Trace L sigma gamma ell cell field) = 0

def ComplementCancellationGoal (admissible : Admissible L sigma gamma ell) : Prop :=
  (∀ grade (field : apComplementRange L sigma gamma ell grade), APPlanarDivergenceZero grade field.val) ∧
  (∀ (field : APSmooth L sigma gamma ell 2) (cell : ℤ),
    apSmoothJet admissible 2 cell (apSmoothQrad L sigma gamma ell field) =
      apSmoothJet admissible 2 cell field - (1 / 2 : ℂ) •
        (equivariantAverageJet (apSmoothJet admissible 2 cell field) +
          reflectedVectorJet (equivariantAverageJet (apSmoothJet admissible 2 cell field)))) ∧
  (∀ (data : CompensatedData L sigma gamma ell) (field : APSmooth L sigma gamma ell 3),
    circularRows admissible (data.1, data.2 - apSmoothComplement L sigma gamma ell field) =
      circularRows admissible data) ∧
  (∀ core : circularCompensatedCore admissible,
    circularForce admissible core.val = circularForceInner admissible core.val)

def errorForce (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) :
    APSmooth L sigma gamma ell 3 →ₗ[ℂ] APSmooth L sigma gamma ell 2 :=
  (2 : ℂ) • ((apSmoothQrad L sigma gamma ell).comp
    (apSmoothMultiplier admissible data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1))

def errorDeterminant (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) :
    APSmooth L sigma gamma ell 3 →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
  (apSmoothRemoveMean L sigma gamma ell 1).comp ((apSmoothDiv admissible).comp
    (apSmoothMultiplier admissible data.fluxDeviation coherent.2.2.2.2.1))

def errorThird (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) :
    APSmooth L sigma gamma ell 3 →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
  (-2 : ℂ) • ((apSmoothRemoveMean L sigma gamma ell 1).comp
    (apSmoothMultiplier admissible data.rotatedThirdProduct coherent.2.2.2.2.2.2.2.2))

def errorRows (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) :
    APSmooth L sigma gamma ell 3 →ₗ[ℂ] SmoothCapSource L sigma gamma ell :=
  (errorForce admissible data coherent).prod
    ((errorDeterminant admissible data coherent).prod (errorThird admissible data coherent))

def errorCoreTrace (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (grade : ℕ) :
    APSmooth L sigma gamma ell 3 →ₗ[ℂ] APBoundaryGrade L sigma gamma ell 1 (grade + 1) :=
  ((apHighTrace L sigma gamma ell (grade + 1) (by omega)).comp
    (apMultiplier admissible (data.traceDeviation (grade + 1)))).toLinearMap.comp
      (apSmoothGrade L sigma gamma ell 3 (grade + 1))

def errorAugmentedCore (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) (grade : ℕ) :
    APSmooth L sigma gamma ell 3 →ₗ[ℂ] CapAugmentedAmbient L sigma gamma ell grade :=
  hilbertPairLinear ((capSourceGrade grade).comp (errorRows admissible data coherent))
    (errorCoreTrace admissible data grade)

/-- Exact AO28 and actual AM9 range before passing to the specified closures. -/
def SmoothForwardComparison (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation) : Prop :=
  (∀ core : circularCompensatedCore admissible,
    actualRows admissible data coherent (smooth.equivalence core).val - circularRows admissible core.val =
      errorRows admissible data coherent (compensatedReconstruct admissible (smooth.equivalence core).val)) ∧
  (∀ core : circularCompensatedCore admissible,
    circularRows admissible core.val ∈ smoothCapSourceCore admissible) ∧
  (∀ core : currentCompensatedCore admissible data.gaugeDeviation smooth.coherent,
    actualRows admissible data coherent core.val ∈ smoothCapSourceCore admissible)

def capAugmentedRange (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (field : CapAugmentedAmbient L sigma gamma ell grade) : Prop :=
  (WithLp.ofLp field).1 ∈ capSourceClosure admissible grade ∧
    apHighProjection L sigma gamma ell (grade + 1) (WithLp.ofLp field).2 = (WithLp.ofLp field).2

/-- A forward realization, never an inverse record. Core application laws
force the actual maps; the output range is the specified AM9 source closure
and actual high boundary space inside the unchanged AP2/AP3 Hilbert ambient. -/
structure CompletedForwardComparison (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation) (grade : ℕ) (large : 3 ≤ grade) where
  circle : circularCompensatedClosure admissible grade →L[ℂ] CapAugmentedAmbient L sigma gamma ell grade
  current : currentCompensatedClosure admissible data.gaugeDeviation smooth.coherent grade →L[ℂ]
    CapAugmentedAmbient L sigma gamma ell grade
  error : apGrade L sigma gamma ell 3 (grade + 1) →L[ℂ] CapAugmentedAmbient L sigma gamma ell grade
  circleCore : ∀ core, circle (compensatedIntoClosure admissible grade _ core) =
    circularAugmentedCore admissible grade core.val
  currentCore : ∀ core, current (compensatedIntoClosure admissible grade _ core) =
    actualAugmentedCore admissible data coherent grade core.val
  errorCore : ∀ field, error (apSmoothGrade L sigma gamma ell 3 (grade + 1) field) =
    errorAugmentedCore admissible data coherent grade field
  circleRange : ∀ field, capAugmentedRange admissible grade (circle field)
  currentRange : ∀ field, capAugmentedRange admissible grade (current field)
  difference : ∀ field,
    current (completedTransfer smooth grade large field) - circle field =
      error (Grad.GaugeCoefficients.Physical.GaugeTransfer.apCurrentProjection admissible data.gaugeDeviation (grade + 1)
        (completedReconstruct admissible grade (circularCompensatedCore admissible) field))

def ComparisonPolynomialContract (polynomials : ℕ → Polynomial ℝ) : Prop :=
  ∀ grade, NonnegativeCoefficients (polynomials grade) ∧ (polynomials grade).eval 0 = 0 ∧
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ value, 0 ≤ value → value ≤ 1 →
      (polynomials grade).eval value ≤ constant * value

/-- Full original-width AO27–32/AP31–33 target. This is only a checked Prop
interface until its construction theorem is supplied. All constants and one
low ball precede ell, actual seed/base, and the unrestricted high grade. -/
def ActualForwardComparisonGoal (parameters : PhaseParameters) (L radius threshold : ℝ) : Prop :=
  ∃ (primitivePolynomials budgetPolynomials : ℕ → Polynomial ℝ) (referenceBound : ℕ → ℝ),
    ComparisonPolynomialContract primitivePolynomials ∧ ComparisonPolynomialContract budgetPolynomials ∧
    (∀ grade, 0 ≤ referenceBound grade) ∧
    ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
      ∀ (ell rho alpha delta parameter epsilon : ℝ)
        (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
        |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
        ∀ base : ACore parameters 3,
          physicalBudget parameters base rho epsilon 10 < lowRadius →
          physicalBudget parameters base rho epsilon 12 ≤ 1 →
          ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
            primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ threshold ∧
            ComplementCancellationGoal admissible ∧
            ∃ smooth : SmoothCompensatedCoreIsomorphism admissible ledger.val.gaugeDeviation,
              SmoothForwardComparison admissible ledger.val ledger.property.1 smooth ∧
              ∀ grade (large : 3 ≤ grade),
                ∃ realization : CompletedForwardComparison admissible ledger.val ledger.property.1 smooth grade large,
                  ‖realization.circle‖ ≤ referenceBound grade ∧
                  ‖realization.current.comp (completedTransfer smooth grade large) - realization.circle‖ ≤
                    (primitivePolynomials grade).eval
                      (primitiveSize parameters admissible rho alpha delta parameter epsilon base (grade + 3)) ∧
                  ‖realization.current.comp (completedTransfer smooth grade large) - realization.circle‖ ≤
                    (budgetPolynomials grade).eval (physicalBudget parameters base rho epsilon (grade + 7))

end Grad.GaugeCoefficients.Physical.Compensated
