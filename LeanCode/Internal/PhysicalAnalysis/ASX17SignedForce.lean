import ASX16SignedDivergence

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.NonlinearRange Grad.FlatSourceProjection
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.RadialLedger
variable {L sigma gamma ell : ℝ}

theorem smoothSpin_rotation (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (field : APSmooth L sigma gamma ell 2) :
    smoothSpin L sigma gamma ell sign (apSmoothRotation admissible 2 field) =
      apSmoothRotation admissible 1 (smoothSpin L sigma gamma ell sign field) :=
  (apSmoothRotation_valueMap admissible (spinValue (sign : ℂ)) field).symm

private theorem map_force {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (mapping : E →ₗ[ℂ] F) (first second third : E) :
    mapping ((-2 : ℂ) • first - (second + third)) =
      (-2 : ℂ) • mapping first - (mapping second + mapping third) := by
  simp only [map_sub, map_add, map_smul]

/-- The literal circular force, in either actual signed component. -/
theorem smoothSpin_force (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (state : CompensatedData L sigma gamma ell) :
    smoothSpin L sigma gamma ell sign (circularForceInner admissible state) =
      (-2 : ℂ) • ((Complex.I * (sign : ℂ)) • smoothSignedDerivative admissible 1 (-sign) state.1) -
      (apSmoothRotation admissible 1 (smoothSpin L sigma gamma ell sign (apSmoothPlanar L sigma gamma ell state.2)) +
        (Complex.I * (sign : ℂ)) • smoothSpin L sigma gamma ell sign (apSmoothPlanar L sigma gamma ell state.2)) := by
  have gradient := (smoothSpin_quarter admissible sign signed (apSmoothGradient admissible state.1)).trans
    (congrArg (fun value : APSmooth L sigma gamma ell 1 => (Complex.I * (sign : ℂ)) • value)
      (smoothSpin_gradient admissible sign state.1))
  exact (map_force (smoothSpin L sigma gamma ell sign)
    (apSmoothQuarter L sigma gamma ell (apSmoothGradient admissible state.1))
    (apSmoothRotation admissible 2 (apSmoothPlanar L sigma gamma ell state.2))
    (apSmoothQuarter L sigma gamma ell (apSmoothPlanar L sigma gamma ell state.2))).trans
      (congrArg₂ (fun first second : APSmooth L sigma gamma ell 1 => first - second)
        (congrArg (fun value : APSmooth L sigma gamma ell 1 => (-2 : ℂ) • value) gradient)
        (congrArg₂ (fun first second : APSmooth L sigma gamma ell 1 => first + second)
          (smoothSpin_rotation admissible sign _) (smoothSpin_quarter admissible sign signed _)))

private theorem rotate_force {E : Type*} [AddCommGroup E] [Module ℂ E]
    (mode sign : ℤ) (gradient field : E) :
    (-2 : ℂ) • ((Complex.I * (sign : ℂ)) • gradient) -
      ((Complex.I * ((mode + sign : ℤ) : ℂ)) • field + (Complex.I * (sign : ℂ)) • field) =
      (-2 * Complex.I * (sign : ℂ)) • gradient - (Complex.I * ((mode + 2 * sign : ℤ) : ℂ)) • field := by
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  module

theorem smoothSpin_force_mode (admissible : Admissible L sigma gamma ell)
    (mode sign : ℤ) (signed : sign = 1 ∨ sign = -1) (state : CompensatedData L sigma gamma ell)
    (rotates : apSmoothRotation admissible 1 (smoothSpin L sigma gamma ell sign (apSmoothPlanar L sigma gamma ell state.2)) =
      (Complex.I * ((mode + sign : ℤ) : ℂ)) • smoothSpin L sigma gamma ell sign (apSmoothPlanar L sigma gamma ell state.2)) :
    smoothSpin L sigma gamma ell sign (circularForceInner admissible state) =
      (-2 * Complex.I * (sign : ℂ)) • smoothSignedDerivative admissible 1 (-sign) state.1 -
        (Complex.I * ((mode + 2 * sign : ℤ) : ℂ)) • smoothSpin L sigma gamma ell sign (apSmoothPlanar L sigma gamma ell state.2) :=
  (smoothSpin_force admissible sign signed state).trans
    ((congrArg (fun value : APSmooth L sigma gamma ell 1 =>
      (-2 : ℂ) • ((Complex.I * (sign : ℂ)) • smoothSignedDerivative admissible 1 (-sign) state.1) -
        (value + (Complex.I * (sign : ℂ)) • smoothSpin L sigma gamma ell sign (apSmoothPlanar L sigma gamma ell state.2))) rotates).trans
      (rotate_force mode sign _ _))

/-- Spin components of the stored planar remainder, as opposed to the reconstructed vector. -/
theorem exceptionalState_spin (admissible : Admissible L sigma gamma ell) (sign direction : ℤ)
    (source : SmoothCapSource L sigma gamma ell) :
    smoothSpin L sigma gamma ell direction (apSmoothPlanar L sigma gamma ell (exceptionalState admissible sign source).2) =
      smoothSpin L sigma gamma ell direction (exceptionalPlanar admissible sign source) -
        smoothSignedDerivative admissible 1 (-direction) (exceptionalTheta admissible sign source) :=
  (congrArg (smoothSpin L sigma gamma ell direction) (exceptionalState_planar admissible sign source)).trans
    (((smoothSpin L sigma gamma ell direction).map_sub _ _).trans
      (congrArg (fun value : APSmooth L sigma gamma ell 1 =>
        smoothSpin L sigma gamma ell direction (exceptionalPlanar admissible sign source) - value)
        (smoothSpin_gradient admissible direction (exceptionalTheta admissible sign source))))

end Grad.ActualExceptionalInverse
