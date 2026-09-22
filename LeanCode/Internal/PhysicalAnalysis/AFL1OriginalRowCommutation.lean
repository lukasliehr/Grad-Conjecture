import AFT4ActualNonexceptionalUniqueness
import AEN16ActualNativeExceptionalConsumer
import ANM8ActualMeanConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
namespace Grad.FullReferenceUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Envelope
open Grad.RawCircularSectors Grad.ActualNonexceptionalInverse Grad.ActualScalarResidual
variable {L sigma gamma ell : ℝ}

theorem angular_removeMean_commute (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (field : APSmooth L sigma gamma ell 1) :
    apSmoothRemoveMean L sigma gamma ell 1 (apSmoothAngularMode L sigma gamma ell 1 mode field) =
      apSmoothAngularMode L sigma gamma ell 1 mode (apSmoothRemoveMean L sigma gamma ell 1 field) := by
  apply apSmoothJet_ext admissible
  intro cell
  have left := (apSmoothRemoveMean_jet admissible _ cell).trans
    (congrArg (fun jet : ClosedJet 1 => jet - angularClosedJet 0 jet) (apSmoothAngularMode_jet admissible mode field cell))
  have right := (apSmoothAngularMode_jet admissible mode _ cell).trans
    (congrArg (angularClosedJet mode) (apSmoothRemoveMean_jet admissible field cell))
  have closed (jet : ClosedJet 1) : angularClosedJet mode jet - angularClosedJet 0 (angularClosedJet mode jet) =
      angularClosedJet mode (jet - angularClosedJet 0 jet) := by
    exact (congrArg (fun value : ClosedJet 1 => angularClosedJet mode jet - value)
      (angularClosedJet_commute 0 mode jet)).trans (map_sub (angularClosedJetLinear 1 mode) jet (angularClosedJet 0 jet)).symm
  exact left.trans ((closed _).trans right.symm)

private theorem force_map {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (project quarter rotation : E →ₗ[ℂ] E) (scalar : F →ₗ[ℂ] F) (gradient : F →ₗ[ℂ] E)
    (turns : ∀ v, project (quarter v) = quarter (project v))
    (rotates : ∀ v, rotation (project v) = project (rotation v))
    (grads : ∀ v, project (gradient v) = gradient (scalar v)) (theta : F) (vector : E) :
    (-2 : ℂ) • quarter (gradient (scalar theta)) - (rotation (project vector) + quarter (project vector)) =
      project ((-2 : ℂ) • quarter (gradient theta) - (rotation vector + quarter vector)) := by
  rw [map_sub, map_smul, map_add, turns, grads, rotates, turns]

theorem circularForceInner_rawState (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (state : CompensatedData L sigma gamma ell) :
    circularForceInner admissible (rawStateProjector L sigma gamma ell mode state) =
      apSmoothRawVector L sigma gamma ell mode (circularForceInner admissible state) := by
  have planar := congrArg (fun vector : APSmooth L sigma gamma ell 2 =>
    (-2 : ℂ) • apSmoothQuarter L sigma gamma ell
      (apSmoothGradient admissible (apSmoothAngularMode L sigma gamma ell 1 mode state.1)) -
      (apSmoothRotation admissible 2 vector + apSmoothQuarter L sigma gamma ell vector))
    (apSmoothRawStored_planar admissible mode state.2)
  exact planar.trans (force_map (apSmoothRawVector L sigma gamma ell mode) (apSmoothQuarter L sigma gamma ell)
    (apSmoothRotation admissible 2) (apSmoothAngularMode L sigma gamma ell 1 mode) (apSmoothGradient admissible)
    (apSmoothRawVector_quarter admissible mode) (apSmoothRotation_rawVector admissible mode)
    (apSmoothRawVector_gradient admissible mode) state.1 (apSmoothPlanar L sigma gamma ell state.2))

theorem circularForce_rawState (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (state : CompensatedData L sigma gamma ell) :
    circularForce admissible (rawStateProjector L sigma gamma ell mode state) =
      apSmoothRawVector L sigma gamma ell mode (circularForce admissible state) :=
  (congrArg (apSmoothQrad L sigma gamma ell) (circularForceInner_rawState admissible mode state)).trans
    (apSmoothRawVector_Qrad admissible mode (circularForceInner admissible state)).symm

theorem circularDeterminant_rawState (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (state : CompensatedData L sigma gamma ell) :
    circularDeterminant admissible (rawStateProjector L sigma gamma ell mode state) =
      apSmoothAngularMode L sigma gamma ell 1 mode (circularDeterminant admissible state) := by
  have divergence := (congrArg (apSmoothDiv admissible) (rawStateProjector_reconstruct admissible mode state)).trans
    (apSmoothDiv_rawStored admissible mode (compensatedReconstruct admissible state))
  have removed := (congrArg (apSmoothRemoveMean L sigma gamma ell 1) divergence).trans
    (angular_removeMean_commute admissible mode (apSmoothDiv admissible (compensatedReconstruct admissible state)))
  exact (congrArg Neg.neg removed).trans (map_neg (apSmoothAngularMode L sigma gamma ell 1 mode)
    (apSmoothRemoveMean L sigma gamma ell 1 (apSmoothDiv admissible (compensatedReconstruct admissible state)))).symm

theorem circularThird_rawState (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (state : CompensatedData L sigma gamma ell) :
    circularThird admissible (rawStateProjector L sigma gamma ell mode state) =
      apSmoothAngularMode L sigma gamma ell 1 mode (circularThird admissible state) :=
  (congrArg (apSmoothRotation admissible 1) (apSmoothRawStored_scalar admissible mode state.2)).trans
    (apSmoothRotation_angular admissible mode (apSmoothScalar L sigma gamma ell state.2))

/-- Every actual interior row commutes with the original raw sector projector. -/
theorem circularRows_rawState (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (state : CompensatedData L sigma gamma ell) :
    circularRows admissible (rawStateProjector L sigma gamma ell mode state) =
      rawSourceProjector L sigma gamma ell mode (circularRows admissible state) :=
  congrArg₂ Prod.mk (circularForce_rawState admissible mode state)
    (congrArg₂ Prod.mk (circularDeterminant_rawState admissible mode state) (circularThird_rawState admissible mode state))

private theorem complement_map {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (mapping : E →ₗ[ℂ] F) (stateProject : ℤ → E →ₗ[ℂ] E) (sourceProject : ℤ → F →ₗ[ℂ] F)
    (commutes : ∀ mode state, mapping (stateProject mode state) = sourceProject mode (mapping state)) (state : E) :
    mapping (state - (stateProject 0 state + stateProject 2 state + stateProject (-2) state)) =
      mapping state - (sourceProject 0 (mapping state) + sourceProject 2 (mapping state) + sourceProject (-2) (mapping state)) := by
  rw [map_sub, map_add, map_add, commutes, commutes, commutes]

theorem circularRows_rawComplement (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) :
    circularRows admissible (rawStateComplement L sigma gamma ell state) =
      rawSourceComplement L sigma gamma ell (circularRows admissible state) :=
  complement_map (circularRows admissible) (rawStateProjector L sigma gamma ell) (rawSourceProjector L sigma gamma ell)
    (circularRows_rawState admissible) state

end Grad.FullReferenceUniqueness
