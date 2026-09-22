import GQF13TangentialRotation

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

variable {L sigma gamma ell : ℝ}

theorem apSmoothTangential_quarter_rotation (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) :
    apSmoothTangential L sigma gamma ell
      (apSmoothQuarter L sigma gamma ell (apSmoothRotation admissible 2 field)) =
        -apSmoothTangential L sigma gamma ell field := by
  apply apSmoothJet_ext admissible
  intro cell
  have first := (apSmoothValueMap_jet admissible quarterValueMap (apSmoothRotation admissible 2 field) cell).trans
    (congrArg (valueMapJet quarterValueMap) (apSmoothRotation_jet admissible field cell))
  exact (apSmoothTangential_jet admissible _ cell).trans
    ((congrArg tangentialJet first).trans
      ((tangentialJet_quarter_rotation _).trans
        ((congrArg (fun jet : ClosedJet 2 => -jet) (apSmoothTangential_jet admissible field cell).symm).trans
          (map_neg (apSmoothJet admissible 2 cell) _).symm)))

theorem apSmoothTangential_gradient (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 1) (meanZero : APSmoothMeanZero admissible field) :
    apSmoothTangential L sigma gamma ell (apSmoothGradient admissible field) = 0 := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothTangential_jet admissible _ cell).trans
    ((congrArg tangentialJet (apSmoothGradient_jet admissible field cell)).trans
      ((tangentialJet_gradient _ (meanZero cell)).trans (map_zero (apSmoothJet admissible 2 cell)).symm))

theorem circularRemainder_complement_zero (admissible : Admissible L sigma gamma ell)
    (state : circularCompensatedCore admissible) :
    apSmoothComplement L sigma gamma ell state.val.2 = 0 := by
  have meanZero := ((mem_compensatedFlatCore admissible state.val).mp state.property.1).1.1
  have covariant := apSmoothCovariant_complement_zero admissible state.val.1 meanZero
  have total := state.property.2
  change apSmoothComplement L sigma gamma ell
    (apSmoothCovariant admissible state.val.1 + state.val.2) = 0 at total
  have expanded := (map_add (apSmoothComplement L sigma gamma ell)
    (apSmoothCovariant admissible state.val.1) state.val.2).symm.trans total
  have reduced := congrArg (fun value : APSmooth L sigma gamma ell 3 =>
    value + apSmoothComplement L sigma gamma ell state.val.2) covariant
  exact (zero_add _).symm.trans (reduced.symm.trans expanded)

theorem radial_force_fixed_algebra {V : Type*} [AddCommGroup V] [Module ℂ V]
    (J T R : V →ₗ[ℂ] V) (square : ∀ field, J (J field) = -field)
    (rotation : ∀ field, T (J (R field)) = -T field)
    (gradient vector : V) (gradientZero : T gradient = 0) (vectorZero : T vector = 0) :
    let force := (-2 : ℂ) • J gradient - (R vector + J vector)
    force + J (T (J force)) = force := by
  dsimp only
  rw [map_sub, map_smul, map_add, square, square, map_sub, map_smul,
    map_neg, map_add, rotation, map_neg, gradientZero, vectorZero,
    neg_zero, smul_zero, add_zero, sub_zero, map_zero, add_zero]

/-- The retained radial projection is redundant precisely on the actual
circular compensated gauge domain, with its original mean and compensation. -/
theorem circularForce_eq_inner (admissible : Admissible L sigma gamma ell)
    (state : circularCompensatedCore admissible) :
    circularForce admissible state.val = circularForceInner admissible state.val := by
  have meanZero := ((mem_compensatedFlatCore admissible state.val).mp state.property.1).1.1
  have vectorZero := (apSmoothPlanar_complement admissible state.val.2).symm.trans
    ((congrArg (apSmoothPlanar L sigma gamma ell) (circularRemainder_complement_zero admissible state)).trans
      (map_zero _))
  exact radial_force_fixed_algebra (apSmoothQuarter L sigma gamma ell)
    (apSmoothTangential L sigma gamma ell) (apSmoothRotation admissible 2)
    (apSmoothQuarter_square admissible) (apSmoothTangential_quarter_rotation admissible)
    (apSmoothGradient admissible state.val.1) (apSmoothPlanar L sigma gamma ell state.val.2)
    (apSmoothTangential_gradient admissible state.val.1 meanZero) vectorZero

theorem actualComplementCancellation (admissible : Admissible L sigma gamma ell) :
    ComplementCancellationGoal admissible :=
  ⟨actualComplementDivergence L sigma gamma ell, apSmoothQrad_jet admissible,
    circularRows_complement_cancellation admissible, circularForce_eq_inner admissible⟩

end Grad.GaugeCoefficients.Physical.Compensated
