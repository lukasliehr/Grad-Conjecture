import GQE3APContractions

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

theorem apAngularMean_trace {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (large : 2 ≤ grade)
    (field : apGrade L sigma gamma ell dimension grade) (cell : ℤ) :
    apTrace admissible large cell (apAngularMean L sigma gamma ell dimension grade field) =
      cMapAngular dimension 0 (apTrace admissible large cell field) := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := grade) L sigma gamma ell)
    (isClosed_eq ((apTrace admissible large cell).continuous.comp
      (apAngularMean L sigma gamma ell dimension grade).continuous)
      ((cMapAngular dimension 0).continuous.comp (apTrace admissible large cell).continuous)) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apAngularMean_core, apTrace_core, apTrace_core]
  apply ContinuousMap.ext
  intro point
  exact (closedCharacterProjection_jet 0 (core cell) point).symm

theorem apSmoothAngularMean_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) (cell : ℤ) :
    apSmoothJet admissible dimension cell (apSmoothAngularMean L sigma gamma ell dimension field) =
      angularClosedJet 0 (apSmoothJet admissible dimension cell field) := by
  apply closedJet_eq_of_value_eq
  change (apFamilyJet (apSmoothAngularMean L sigma gamma ell dimension field).val _ cell).value = _
  rw [apFamilyJet_value_trace admissible (apSmoothAngularMean L sigma gamma ell dimension field).val
    (apSmoothAngularMean L sigma gamma ell dimension field).property (by omega : 2 ≤ 2) cell]
  change apTrace admissible (by omega : 2 ≤ 2) cell
    (apAngularMean L sigma gamma ell dimension 2 (field.val 2)) = _
  rw [apAngularMean_trace, ← apFamilyJet_value_trace admissible field.val field.property (by omega : 2 ≤ 2) cell]
  apply ContinuousMap.ext
  intro point
  exact closedCharacterProjection_jet 0 (apSmoothJet admissible dimension cell field) point

def apSmoothRemoveMean (L sigma gamma ell : ℝ) (dimension : ℕ) :
    APSmooth L sigma gamma ell dimension →ₗ[ℂ] APSmooth L sigma gamma ell dimension :=
  LinearMap.id - apSmoothAngularMean L sigma gamma ell dimension

def apSmoothRadial {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) :
    APSmooth L sigma gamma ell 3 →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
  apSmoothFixedJet admissible radialRowJet

def apSmoothTangent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) :
    APSmooth L sigma gamma ell 3 →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
  apSmoothFixedJet admissible tangentRowJet

def apSmoothProjectedTangent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) :
    APSmooth L sigma gamma ell 3 →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
  (apSmoothRemoveMean L sigma gamma ell 1).comp (apSmoothTangent admissible)

theorem apSmoothRadial_complement {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) :
    apSmoothRadial admissible (apSmoothComplement L sigma gamma ell field) = 0 := by
  apply Subtype.ext
  funext grade
  exact apRadialContraction_complement admissible grade (field.val grade)

theorem apSmoothProjectedTangent_complement {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (field : APSmooth L sigma gamma ell 3) :
    apSmoothProjectedTangent admissible (apSmoothComplement L sigma gamma ell field) = 0 := by
  apply Subtype.ext
  funext grade
  exact apMeanFree_tangent_complement admissible grade (field.val grade)

theorem apSmoothRadial_circle {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) :
    apSmoothRadial admissible (apSmoothCircle L sigma gamma ell field) = apSmoothRadial admissible field := by
  change apSmoothRadial admissible (field - apSmoothComplement L sigma gamma ell field) = _
  exact (map_sub (apSmoothRadial admissible) field (apSmoothComplement L sigma gamma ell field)).trans
    ((congrArg (fun removed : APSmooth L sigma gamma ell 1 => apSmoothRadial admissible field - removed)
      (apSmoothRadial_complement admissible field)).trans (sub_zero _))

theorem apSmoothProjectedTangent_circle {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) :
    apSmoothProjectedTangent admissible (apSmoothCircle L sigma gamma ell field) =
      apSmoothProjectedTangent admissible field := by
  change apSmoothProjectedTangent admissible (field - apSmoothComplement L sigma gamma ell field) = _
  exact (map_sub (apSmoothProjectedTangent admissible) field (apSmoothComplement L sigma gamma ell field)).trans
    ((congrArg (fun removed : APSmooth L sigma gamma ell 1 => apSmoothProjectedTangent admissible field - removed)
      (apSmoothProjectedTangent_complement admissible field)).trans (sub_zero _))

end Grad.GaugeCoefficients.Physical.Compensated
