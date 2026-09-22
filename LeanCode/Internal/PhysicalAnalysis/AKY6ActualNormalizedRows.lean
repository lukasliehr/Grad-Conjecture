import AKY5UncompressedSecondOrder
import GQF11SmoothComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.CartesianUncompressed
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.ActualScalarForcing Grad.RawCircularSectors

variable {L sigma gamma ell : ℝ}

def actualErQuotient (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) : APSmooth L sigma gamma ell 3 :=
  apSmoothCircle L sigma gamma ell (compensatedReconstruct admissible state)

def actualErForceCorrection (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (field : APSmooth L sigma gamma ell 3) : APSmooth L sigma gamma ell 2 :=
  (2 : ℂ) • apSmoothQrad L sigma gamma ell
    (apSmoothMultiplier admissible data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1 field)

def actualErThirdCorrection (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (field : APSmooth L sigma gamma ell 3) : APSmooth L sigma gamma ell 1 :=
  (2 : ℂ) • apSmoothRemoveMean L sigma gamma ell 1
    (apSmoothMultiplier admissible data.rotatedThirdProduct coherent.2.2.2.2.2.2.2.2 field)

def actualErFlux (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (field : APSmooth L sigma gamma ell 3) : APSmooth L sigma gamma ell 3 :=
  apSmoothMultiplier admissible data.fluxDeviation coherent.2.2.2.2.1 field

theorem apPlanar_covariant (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) :
    apSmoothPlanar L sigma gamma ell (apSmoothCovariant admissible theta) =
      apSmoothGradient admissible theta := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothValueMap_jet admissible planarPartMap _ cell).trans
    ((congrArg (valueMapJet planarPartMap) (apSmoothCovariant_jet admissible theta cell)).trans
      ((planarCovariantJet _ _).trans (apSmoothGradient_jet admissible theta cell).symm))

theorem apScalar_covariant (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) :
    apSmoothScalar L sigma gamma ell (apSmoothCovariant admissible theta) =
      apSmoothAxial L sigma gamma ell 1 theta := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothValueMap_jet admissible toroidalPartMap _ cell).trans
    ((congrArg (valueMapJet toroidalPartMap) (apSmoothCovariant_jet admissible theta cell)).trans
      ((scalarCovariantJet _ _).trans (apSmoothAxial_jet admissible theta cell).symm))

theorem circularForce_backward_inner (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell)
    (mean : APSmoothMeanZero admissible state.1) :
    circularForce admissible state =
      circularForceInner admissible (compensatedBackward L sigma gamma ell state) := by
  have same := congrArg Prod.fst (circularRows_backward admissible state)
  have vectorZero := (actualQuotient_componentGauges admissible state.2).1
  have fixed := radial_force_fixed_algebra (apSmoothQuarter L sigma gamma ell)
    (apSmoothTangential L sigma gamma ell) (apSmoothRotation admissible 2)
    (apSmoothQuarter_square admissible) (apSmoothTangential_quarter_rotation admissible)
    (apSmoothGradient admissible state.1)
    (apSmoothPlanar L sigma gamma ell (apSmoothCircle L sigma gamma ell state.2))
    (apSmoothTangential_gradient admissible state.1 mean) vectorZero
  exact same.symm.trans fixed

private theorem normalize_force_algebra {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rotation quarter : V →ₗ[ℂ] V) (gradient rotated vector remainder : V)
    (commutator : rotation gradient = rotated + quarter gradient)
    (reconstruct : vector = gradient + remainder) :
    (-2 : ℂ) • quarter gradient - (rotation remainder + quarter remainder) =
      rotated - (rotation vector + quarter vector) := by
  rw [reconstruct, map_add, map_add, commutator]
  module

theorem circularForce_normalized (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell)
    (mean : APSmoothMeanZero admissible state.1) :
    circularForce admissible state =
      apSmoothGradient admissible (apSmoothRotation admissible 1 state.1) -
        (apSmoothRotation admissible 2 (apSmoothPlanar L sigma gamma ell (actualErQuotient admissible state)) +
          apSmoothQuarter L sigma gamma ell (apSmoothPlanar L sigma gamma ell (actualErQuotient admissible state))) := by
  have representation := (compensatedBackward_reconstruct admissible state mean).symm
  have planar := congrArg (apSmoothPlanar L sigma gamma ell) representation
  have expanded := (apSmoothPlanar L sigma gamma ell).map_add
    (apSmoothCovariant admissible state.1)
    (apSmoothCircle L sigma gamma ell state.2)
  have parts := congrArg (fun value : APSmooth L sigma gamma ell 2 =>
    value + apSmoothPlanar L sigma gamma ell (apSmoothCircle L sigma gamma ell state.2))
      (apPlanar_covariant admissible state.1)
  have vectorRepresentation := planar.trans (expanded.trans parts)
  exact (circularForce_backward_inner admissible state mean).trans
    (normalize_force_algebra (apSmoothRotation admissible 2) (apSmoothQuarter L sigma gamma ell)
      (apSmoothGradient admissible state.1)
      (apSmoothGradient admissible (apSmoothRotation admissible 1 state.1))
      (apSmoothPlanar L sigma gamma ell (actualErQuotient admissible state))
      (apSmoothPlanar L sigma gamma ell (apSmoothCircle L sigma gamma ell state.2))
      (apRotation_gradient_actual admissible state.1) vectorRepresentation)

/-- The force identity is the accepted actual physical row, with its complete
rotated-frame multiplication and the original fixed quotient. -/
theorem actualForce_normalized (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (state : CompensatedData L sigma gamma ell)
    (mean : APSmoothMeanZero admissible state.1) :
    actualForce admissible data coherent state -
      actualErForceCorrection admissible data coherent (compensatedReconstruct admissible state) =
        apSmoothGradient admissible (apSmoothRotation admissible 1 state.1) -
          (apSmoothRotation admissible 2 (apSmoothPlanar L sigma gamma ell (actualErQuotient admissible state)) +
            apSmoothQuarter L sigma gamma ell (apSmoothPlanar L sigma gamma ell (actualErQuotient admissible state))) := by
  have difference := projected_add_difference (apSmoothQrad L sigma gamma ell)
    (circularForceInner admissible state)
    (apSmoothMultiplier admissible data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1
      (compensatedReconstruct admissible state))
  have sum := (sub_eq_iff_eq_add).mp difference
  have cancel := (congrArg (fun value : APSmooth L sigma gamma ell 2 => value -
    actualErForceCorrection admissible data coherent (compensatedReconstruct admissible state)) sum).trans
      (add_sub_cancel_left _ _)
  exact cancel.trans (circularForce_normalized admissible state mean)

end Grad.CartesianUncompressed
