import GQD3BoundedExtensions

noncomputable section
set_option maxHeartbeats 800000
open scoped ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.GaugeTransfer

theorem angularDerivative_of_dense {C E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {L sigma gamma ell : ℝ} {dimension grade : ℕ} (embed : C → E) (dense : DenseRange embed)
    (value derivative : E →L[ℂ] apGrade L sigma gamma ell dimension grade)
    (coreLaw : ∀ core, APHasAngularDerivative L sigma gamma ell (value (embed core)) (derivative (embed core)))
    (field : E) : APHasAngularDerivative L sigma gamma ell (value field) (derivative field) := by
  intro cell testCell vector test smooth compact supported
  exact isClosed_property dense
    (isClosed_eq
      ((apDiskPairing dimension testCell vector test smooth compact).continuous.comp
        ((apL2Trace L sigma gamma ell cell).continuous.comp derivative.continuous))
      ((angularWeakPairing dimension testCell vector test smooth compact).continuous.comp
        ((apL2Trace L sigma gamma ell cell).continuous.comp value.continuous)))
    (fun core => coreLaw core cell testCell vector test smooth compact supported) field

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

def compensatedClosureEntry (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (index : Fin 5) : compensatedClosure admissible grade core →L[ℂ]
      apGrade L sigma gamma ell (graphDimension index) (graphGrade grade index) :=
  LinearMap.mkContinuous
    { toFun := fun field => field.val index
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun field => (PiLp.norm_apply_le field.val index).trans_eq (one_mul ‖field‖).symm)

theorem compensatedClosure_planarRotation (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (field : compensatedClosure admissible grade core) :
    APHasAngularDerivative L sigma gamma ell (field.val 1) (field.val 2) := by
  exact angularDerivative_of_dense (compensatedIntoClosure admissible grade core)
    (compensatedIntoClosure_denseRange admissible grade core)
    (compensatedClosureEntry admissible grade core 1) (compensatedClosureEntry admissible grade core 2)
    (fun data => apSmoothRotation_weak admissible
      (apSmoothValueMap L sigma gamma ell planarPartMap data.val.2) (grade + 1)) field

theorem compensatedClosure_scalarRotation (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (field : compensatedClosure admissible grade core) :
    APHasAngularDerivative L sigma gamma ell (field.val 3) (field.val 4) := by
  exact angularDerivative_of_dense (compensatedIntoClosure admissible grade core)
    (compensatedIntoClosure_denseRange admissible grade core)
    (compensatedClosureEntry admissible grade core 3) (compensatedClosureEntry admissible grade core 4)
    (fun data => apSmoothRotation_weak admissible
      (apSmoothValueMap L sigma gamma ell toroidalPartMap data.val.2) (grade + 1)) field

theorem angularDerivative_zero (dimension grade : ℕ) :
    APHasAngularDerivative L sigma gamma ell (0 : apGrade L sigma gamma ell dimension grade) 0 := by
  intro cell testCell vector test smooth compact supported
  simp only [map_zero]

/-- The closure has no independent rotation coordinates. Its genuine
AP2 weak rotation slots are determined by the actual three field slots. -/
theorem compensatedClosure_zero_of_fields_zero (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (field : compensatedClosure admissible grade core)
    (theta : field.val 0 = 0) (planar : field.val 1 = 0) (scalar : field.val 3 = 0) : field = 0 := by
  have planarZeroLaw : APHasAngularDerivative L sigma gamma ell (field.val 1) 0 :=
    planar.symm ▸ angularDerivative_zero (L := L) (sigma := sigma) (gamma := gamma) (ell := ell) 2 (grade + 1)
  have scalarZeroLaw : APHasAngularDerivative L sigma gamma ell (field.val 3) 0 :=
    scalar.symm ▸ angularDerivative_zero (L := L) (sigma := sigma) (gamma := gamma) (ell := ell) 1 (grade + 1)
  have planarRotation := (compensatedClosure_planarRotation admissible grade core field).unique planarZeroLaw
  have scalarRotation := (compensatedClosure_scalarRotation admissible grade core field).unique scalarZeroLaw
  apply Subtype.ext
  apply PiLp.ext
  intro index
  fin_cases index
  · exact theta
  · exact planar
  · exact planarRotation
  · exact scalar
  · exact scalarRotation

end Grad.GaugeCoefficients.Physical.Compensated
