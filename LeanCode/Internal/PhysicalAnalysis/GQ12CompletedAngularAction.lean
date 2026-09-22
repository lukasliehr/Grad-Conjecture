import GQ11AngularWeakCore

noncomputable section

set_option maxHeartbeats 1600000

open scoped ContDiff

namespace Grad.GaugeCoefficients.Physical.GaugeTransfer

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GenericCarriers
open Grad.NonlinearRange Grad.GaugeCoefficients.Physical.RadialLedger

/-- Distributional Cartesian rotation on the faithful original AP2
completion, tested in the actual unweighted cell L2 realizations. -/
def APHasAngularDerivative {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (field derivative : apGrade L sigma gamma ell dimension grade) : Prop :=
  ∀ (cell testCell : ℤ) (vector : PhysicalValue dimension) (test : Grad.PDEBootstrap.Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test), tsupport test ⊆ openUnitDisk →
    apDiskPairing dimension testCell vector test smooth compact (apL2Trace L sigma gamma ell cell derivative) =
      angularWeakPairing dimension testCell vector test smooth compact (apL2Trace L sigma gamma ell cell field)

theorem APHasAngularDerivative.unique {dimension grade : ℕ} {L sigma gamma ell : ℝ}
    {field first second : apGrade L sigma gamma ell dimension grade}
    (firstLaw : APHasAngularDerivative L sigma gamma ell field first)
    (secondLaw : APHasAngularDerivative L sigma gamma ell field second) : first = second := by
  apply apL2Trace_ext L sigma gamma ell
  intro cell
  apply apDiskPairing_separates
  intro testCell vector test smooth compact supported
  rw [firstLaw cell testCell vector test smooth compact supported,
    secondLaw cell testCell vector test smooth compact supported]

theorem apComplement_angular_weak (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : apGrade L sigma gamma ell 3 grade) :
    APHasAngularDerivative L sigma gamma ell (apComplement L sigma gamma ell grade field)
      (apStoredQuarter L sigma gamma ell grade (apComplement L sigma gamma ell grade field)) := by
  intro cell testCell vector test smooth compact supported
  apply isClosed_property (apFiniteInto_denseRange (dimension := 3) (grade := grade) L sigma gamma ell)
    (isClosed_eq
      ((apDiskPairing 3 testCell vector test smooth compact).continuous.comp
        ((apL2Trace L sigma gamma ell cell).continuous.comp
          ((apStoredQuarter L sigma gamma ell grade).continuous.comp (apComplement L sigma gamma ell grade).continuous)))
      ((angularWeakPairing 3 testCell vector test smooth compact).continuous.comp
        ((apL2Trace L sigma gamma ell cell).continuous.comp (apComplement L sigma gamma ell grade).continuous))) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apComplement_core, apStoredQuarter_core, apL2Trace_core, apL2Trace_core]
  change apDiskPairing 3 testCell vector test smooth compact
    (closedContinuousToDiskL2 (valueMapJet storedQuarterMap (fixedComplementJet (core cell))).value) =
    angularWeakPairing 3 testCell vector test smooth compact (closedContinuousToDiskL2 (fixedComplementJet (core cell)).value)
  rw [← rotationJet_fixedComplement]
  exact rotationJet_weak _ testCell vector test smooth compact supported

theorem apComplementRange_angular_weak (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : apGrade L sigma gamma ell 3 grade) (member : field ∈ apComplementRange L sigma gamma ell grade) :
    APHasAngularDerivative L sigma gamma ell field (apStoredQuarter L sigma gamma ell grade field) := by
  have identity := apComplement_angular_weak L sigma gamma ell grade field
  rwa [(apComplementRange_mem_iff L sigma gamma ell grade field).mp member] at identity

theorem apStoredQuarter_L2 (L sigma gamma ell : ℝ) (grade : ℕ) (cell : ℤ)
    (field : apGrade L sigma gamma ell 3 grade) :
    apL2Trace L sigma gamma ell cell (apStoredQuarter L sigma gamma ell grade field) =
      closedOperatorL2 (ContinuousMap.const ClosedDisk storedQuarterMap) (apL2Trace L sigma gamma ell cell field) := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := 3) (grade := grade) L sigma gamma ell)
    (isClosed_eq ((apL2Trace L sigma gamma ell cell).continuous.comp (apStoredQuarter L sigma gamma ell grade).continuous)
      ((closedOperatorL2 (ContinuousMap.const ClosedDisk storedQuarterMap)).continuous.comp
        (apL2Trace L sigma gamma ell cell).continuous)) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apStoredQuarter_core, apL2Trace_core, apL2Trace_core, closedOperatorL2_closed]
  apply congrArg closedContinuousToDiskL2
  apply ContinuousMap.ext
  intro point
  exact valueMapJet_value storedQuarterMap (core cell) point

/-- R restricted to the actual completed V. The target is ambient AP2:
Jv is radial and need not itself be in the tangential range V. -/
def apComplementAngularAction (L sigma gamma ell : ℝ) (grade : ℕ) :
    apComplementRange L sigma gamma ell grade →L[ℂ] apGrade L sigma gamma ell 3 grade :=
  (apStoredQuarter L sigma gamma ell grade).comp (apComplementRange L sigma gamma ell grade).subtypeL

/-- Literal AO3 at every original grade, including 0 and 1: genuine weak
R(v,t)=(Jv,0), sharp norm at most one, and a unique AP2 derivative. -/
theorem actualComplementAngularAction (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : apComplementRange L sigma gamma ell grade) :
    APHasAngularDerivative L sigma gamma ell field.val (apComplementAngularAction L sigma gamma ell grade field) ∧
      ‖apComplementAngularAction L sigma gamma ell grade field‖ ≤ ‖field‖ ∧
      (∀ cell, apL2Trace L sigma gamma ell cell (apComplementAngularAction L sigma gamma ell grade field) =
        closedOperatorL2 (ContinuousMap.const ClosedDisk storedQuarterMap) (apL2Trace L sigma gamma ell cell field.val)) ∧
      ∀ derivative, APHasAngularDerivative L sigma gamma ell field.val derivative →
        derivative = apComplementAngularAction L sigma gamma ell grade field := by
  have weak := apComplementRange_angular_weak L sigma gamma ell grade field.val field.property
  exact ⟨weak, apStoredQuarter_bound L sigma gamma ell grade field.val,
    fun cell => apStoredQuarter_L2 L sigma gamma ell grade cell field.val, fun _ law => law.unique weak⟩

end Grad.GaugeCoefficients.Physical.GaugeTransfer
