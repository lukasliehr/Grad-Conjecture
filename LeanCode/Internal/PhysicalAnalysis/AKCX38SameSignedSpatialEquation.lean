import AKCX37SamePhaseEquationSpatialGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.CellWeights Grad.SpatialDilation

namespace StartupSignedFamily
variable {dimension : ℕ} {L ell : ℝ}

def naturalMoment (family : StartupSignedFamily dimension L ell) (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0)
    (power weight : ℕ) : StartupL2 dimension :=
  ((family.shift power).toNatural lengthNonzero scaleNonzero).moment weight

theorem naturalMoment_same (family : StartupSignedFamily dimension L ell) (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0)
    (power weight : ℕ) : StartupRadialRelated (fun cell _ => cellWeight cell ^ weight)
      (family.naturalMoment lengthNonzero scaleNonzero power weight) (family.moment power) :=
  ((family.shift power).toNatural lengthNonzero scaleNonzero).same.mono (fun _ same => same weight)

end StartupSignedFamily

variable (parameters : PhaseParameters) {L : ℝ} (lengthNonzero : L ≠ 0) (scale : Scale)
    (field : StartupSignedFamily 3 L scale.val) (tensor : Fin 2 → Fin 2 → StartupSignedFamily 3 L scale.val)
    (flux : Fin 2 → StartupSignedFamily 3 L scale.val) (power : ℕ)

def startupSignedPhaseZeroth : StartupL2 3 :=
  startupPhaseEquationZeroth parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le scale.property.1.le scale.property.2
    0 (field.naturalMoment lengthNonzero scale.property.1.ne' power 2)
    (fun outer inner => (tensor outer inner).naturalMoment lengthNonzero scale.property.1.ne' power 2)
    (fun direction => (flux direction).naturalMoment lengthNonzero scale.property.1.ne' power 1)

def startupSignedPhaseFlux (direction : Fin 2) : StartupL2 3 :=
  startupPhaseEquationFlux parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le scale.property.1.le scale.property.2
    (field.naturalMoment lengthNonzero scale.property.1.ne' power 1)
    (fun outer inner => (tensor outer inner).naturalMoment lengthNonzero scale.property.1.ne' power 1)
    (fun direction => (flux direction).moment power) direction

/-- SAME original raw equation, conjugated by its genuine phase at every signed power. -/
theorem startupSame_signedPhase_equation
    (equation : StartupWeakDivDivEquation (field.unweight parameters scale).field 0
      (fun outer inner => ((tensor outer inner).unweight parameters scale).field)
      (fun direction => ((flux direction).unweight parameters scale).field)) :
    StartupWeakDivDivEquation (field.moment power)
      (startupSignedPhaseZeroth parameters lengthNonzero scale field tensor flux power)
      (fun outer inner => (tensor outer inner).moment power)
      (startupSignedPhaseFlux parameters lengthNonzero scale field tensor flux power) := by
  have first (family : StartupSignedFamily 3 L scale.val) :=
    family.naturalMoment_same lengthNonzero scale.property.1.ne' power 1
  simp only [pow_one] at first
  exact startupSame_phase_divDiv parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le scale.property.1.le scale.property.2
    (field.moment power) ((field.unweight parameters scale).moment power) 0 0
    (field.naturalMoment lengthNonzero scale.property.1.ne' power 1)
    (field.naturalMoment lengthNonzero scale.property.1.ne' power 2)
    (fun outer inner => (tensor outer inner).moment power)
    (fun outer inner => ((tensor outer inner).unweight parameters scale).moment power)
    (fun outer inner => (tensor outer inner).naturalMoment lengthNonzero scale.property.1.ne' power 1)
    (fun outer inner => (tensor outer inner).naturalMoment lengthNonzero scale.property.1.ne' power 2)
    (fun direction => (flux direction).moment power)
    (fun direction => ((flux direction).unweight parameters scale).moment power)
    (fun direction => (flux direction).naturalMoment lengthNonzero scale.property.1.ne' power 1)
    (field.unweight_phase parameters scale power) StartupRadialRelated.zero
    (fun outer inner => (tensor outer inner).unweight_phase parameters scale power)
    (fun direction => (flux direction).unweight_phase parameters scale power)
    (first field) (field.naturalMoment_same lengthNonzero scale.property.1.ne' power 2)
    (fun outer inner => first (tensor outer inner))
    (fun outer inner => (tensor outer inner).naturalMoment_same lengthNonzero scale.property.1.ne' power 2)
    (fun direction => first (flux direction))
    (startupSame_signed_weakDivDiv_zero (field.unweight parameters scale)
      (fun outer inner => (tensor outer inner).unweight parameters scale)
      (fun direction => (flux direction).unweight parameters scale) equation power)

/-- Completed spatial induction data supply every actual phase remainder graph. -/
theorem startupSame_signedPhase_graphs (order : ℕ)
    (fieldRegular : field.HasSpatialGrade order)
    (tensorRegular : ∀ outer inner, (tensor outer inner).HasSpatialGrade order)
    (fluxRegular : ∀ direction, (flux direction).HasSpatialGrade order) :
    (∃ graph : GraphGrade 3 order 0 openUnitDisk,
      base 3 order openUnitDisk (fun _ => 0) graph = startupSignedPhaseZeroth parameters lengthNonzero scale field tensor flux power) ∧
    (∀ direction, ∃ graph : GraphGrade 3 order 0 openUnitDisk,
      base 3 order openUnitDisk (fun _ => 0) graph = startupSignedPhaseFlux parameters lengthNonzero scale field tensor flux power direction) := by
  have first (family : StartupSignedFamily 3 L scale.val) :=
    family.naturalMoment_same lengthNonzero scale.property.1.ne' power 1
  simp only [pow_one] at first
  exact startupPhaseEquation_spatialGraphs parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le scale.property.1.le scale.property.2
    order (field.moment power)
    (field.naturalMoment lengthNonzero scale.property.1.ne' power 1) (field.naturalMoment lengthNonzero scale.property.1.ne' power 2)
    (fun outer inner => (tensor outer inner).moment power)
    (fun outer inner => (tensor outer inner).naturalMoment lengthNonzero scale.property.1.ne' power 1)
    (fun outer inner => (tensor outer inner).naturalMoment lengthNonzero scale.property.1.ne' power 2)
    (fun direction => (flux direction).moment power)
    (fun direction => (flux direction).naturalMoment lengthNonzero scale.property.1.ne' power 1)
    (fieldRegular power) (fun outer inner => tensorRegular outer inner power) (fun direction => fluxRegular direction power)
    (first field) (field.naturalMoment_same lengthNonzero scale.property.1.ne' power 2)
    (fun outer inner => first (tensor outer inner))
    (fun outer inner => (tensor outer inner).naturalMoment_same lengthNonzero scale.property.1.ne' power 2)
    (fun direction => first (flux direction))

end Grad.CartesianStartup
