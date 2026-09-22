import GQF9SmoothDivergence

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

variable {L sigma gamma ell : ℝ}

theorem linear_force_zero {S V : Type*} [AddCommGroup S] [Module ℂ S]
    [AddCommGroup V] [Module ℂ V] (G : S →ₗ[ℂ] V) (J R Q : V →ₗ[ℂ] V) (v : V)
    (rotation : R v = J v) (projected : Q (J v) = 0) :
    Q ((-2 : ℂ) • J (G 0) - (R v + J v)) = 0 := by
  rw [map_zero, map_zero, smul_zero, zero_sub, rotation, map_neg, map_add, projected,
    zero_add, neg_zero]

theorem circularForce_zero_complement (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) :
    circularForce admissible (0, apSmoothComplement L sigma gamma ell field) = 0 := by
  have planar := apSmoothPlanar_complement admissible field
  have rotation := (congrArg (apSmoothRotation admissible 2) planar).trans
    ((apSmoothRotation_tangential admissible (apSmoothPlanar L sigma gamma ell field)).trans
      (congrArg (apSmoothQuarter L sigma gamma ell) planar.symm))
  have projected := (congrArg (fun value : APSmooth L sigma gamma ell 2 =>
    apSmoothQrad L sigma gamma ell (apSmoothQuarter L sigma gamma ell value)) planar).trans
      (apSmoothQrad_quarter_tangential admissible (apSmoothPlanar L sigma gamma ell field))
  exact linear_force_zero (apSmoothGradient admissible) (apSmoothQuarter L sigma gamma ell)
    (apSmoothRotation admissible 2) (apSmoothQrad L sigma gamma ell)
    (apSmoothPlanar L sigma gamma ell (apSmoothComplement L sigma gamma ell field)) rotation projected

theorem compensatedReconstruct_zero_left (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) : compensatedReconstruct admissible (0, field) = field :=
  (congrArg (fun value : APSmooth L sigma gamma ell 3 => value + field)
    (map_zero (apSmoothCovariant admissible))).trans (zero_add field)

theorem circularDeterminant_zero_complement (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) :
    circularDeterminant admissible (0, apSmoothComplement L sigma gamma ell field) = 0 := by
  have law := (congrArg (fun value : APSmooth L sigma gamma ell 3 =>
    apSmoothRemoveMean L sigma gamma ell 1 (apSmoothDiv admissible value))
      (compensatedReconstruct_zero_left admissible (apSmoothComplement L sigma gamma ell field))).trans
        (apSmoothRemoveMean_div_complement admissible field)
  exact (congrArg (fun value : APSmooth L sigma gamma ell 1 => -value) law).trans neg_zero

theorem circularThird_zero_complement (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) :
    circularThird admissible (0, apSmoothComplement L sigma gamma ell field) = 0 :=
  (congrArg (apSmoothRotation admissible 1) (apSmoothScalar_complement admissible field)).trans
    (apSmoothRotation_mean_zero admissible (apSmoothScalar L sigma gamma ell field))

theorem circularRows_zero_complement (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) :
    circularRows admissible (0, apSmoothComplement L sigma gamma ell field) = 0 :=
  Prod.ext (circularForce_zero_complement admissible field)
    (Prod.ext (circularDeterminant_zero_complement admissible field)
      (circularThird_zero_complement admissible field))

/-- Exact circular correction cancellation on the actual smooth carrier.
No flatness or inverse hypothesis is needed for this three-row identity. -/
theorem circularRows_complement_cancellation (admissible : Admissible L sigma gamma ell)
    (data : CompensatedData L sigma gamma ell) (field : APSmooth L sigma gamma ell 3) :
    circularRows admissible (data.1, data.2 - apSmoothComplement L sigma gamma ell field) =
      circularRows admissible data := by
  have pair : (data.1, data.2 - apSmoothComplement L sigma gamma ell field) =
      data - (0, apSmoothComplement L sigma gamma ell field) := Prod.ext (sub_zero _).symm rfl
  exact (congrArg (circularRows admissible) pair).trans
    ((map_sub (circularRows admissible) data (0, apSmoothComplement L sigma gamma ell field)).trans
      ((congrArg (fun value : SmoothCapSource L sigma gamma ell => circularRows admissible data - value)
        (circularRows_zero_complement admissible field)).trans (sub_zero _)))

end Grad.GaugeCoefficients.Physical.Compensated
