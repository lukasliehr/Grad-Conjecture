import ANF6ActualEliminationBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualScalarForcing
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange Grad.NonlinearDivision
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualAngularInverse Grad.ActualNonexceptionalInverse Grad.RawCircularSectors
variable {L sigma gamma ell : ℝ}

private theorem split_algebra {E F V : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup V]
    [Module ℂ E] [Module ℂ F] [Module ℂ V] (inclusion : E →ₗ[ℂ] V) (scalar : F →ₗ[ℂ] V)
    (gradient stored response : E) (axial extra : F) :
    (inclusion gradient + scalar axial) + (inclusion stored + scalar extra) =
      inclusion (gradient + stored - response) + inclusion response + scalar (axial + extra) := by
  rw [map_sub, map_add, map_add]
  abel

theorem actualReconstruction_split (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell) :
    compensatedReconstruct admissible (reconstructedState admissible theta source) =
      homogeneousLift admissible theta source + forceLift admissible source.1 +
        apSmoothValueMap L sigma gamma ell toroidalInclusionMap
          (apSmoothAxial L sigma gamma ell 1 theta + reconstructedScalar admissible source.2.2) :=
  split_algebra (apSmoothValueMap L sigma gamma ell planarInclusionMap)
    (apSmoothValueMap L sigma gamma ell toroidalInclusionMap)
    (apSmoothGradient admissible theta) (reconstructedVector admissible theta source.1)
    (forceResponse admissible source.1) (apSmoothAxial L sigma gamma ell 1 theta)
    (reconstructedScalar admissible source.2.2)

theorem planarDiv_toroidal_zero (field : ClosedJet 1) :
    planarDivJet (valueMapJet toroidalInclusionMap field) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  change (planarDivJet (valueMapJet toroidalInclusionMap field)).value point 0 = 0
  rw [planarDivJet_value, partialJet_valueMap, partialJet_valueMap, valueMapJet_value, valueMapJet_value]
  simp [toroidalInclusionMap]

theorem div_toroidalLift (admissible : Admissible L sigma gamma ell)
    (scalar : APSmooth L sigma gamma ell 1) :
    apSmoothDiv admissible (apSmoothValueMap L sigma gamma ell toroidalInclusionMap scalar) =
      apSmoothAxial L sigma gamma ell 1 scalar := by
  apply apSmoothJet_ext admissible
  intro cell
  have image := apSmoothValueMap_jet admissible toroidalInclusionMap scalar cell
  have divZero := (congrArg planarDivJet image).trans (planarDiv_toroidal_zero _)
  have toroidal : valueMapJet toroidalPartMap (valueMapJet toroidalInclusionMap (apSmoothJet admissible 1 cell scalar)) =
      apSmoothJet admissible 1 cell scalar := by
    rw [valueMapJet_comp, toroidalPart_toroidalInclusion, valueMapJet_identity]
  exact (apSmoothDiv_jet admissible _ cell).trans
    ((congrArg₂ (fun a b : ClosedJet 1 => a + seedScaledFrequency L ell cell • b) divZero
      ((congrArg (valueMapJet toroidalPartMap) image).trans toroidal)).trans
        ((zero_add _).trans (apSmoothAxial_jet admissible scalar cell).symm))

theorem radial_toroidal_zero (field : ClosedJet 1) :
    apProductJet radialRowJet (valueMapJet toroidalInclusionMap field) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [apProductJet_value, radialRowJet_value, valueMapJet_value, toroidalInclusionMap]

theorem radial_toroidalLift (admissible : Admissible L sigma gamma ell)
    (scalar : APSmooth L sigma gamma ell 1) :
    apSmoothRadial admissible (apSmoothValueMap L sigma gamma ell toroidalInclusionMap scalar) = 0 := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothFixedJet_jet admissible radialRowJet _ cell).trans
    ((congrArg (apProductJet radialRowJet) (apSmoothValueMap_jet admissible toroidalInclusionMap scalar cell)).trans
      ((radial_toroidal_zero _).trans (map_zero _).symm))

private theorem div_split_algebra {E V : Type*} [AddCommGroup E] [AddCommGroup V]
    [Module ℂ E] [Module ℂ V] (div : V →ₗ[ℂ] E) (axial : E →ₗ[ℂ] E)
    (whole homogeneous force toroidal : V) (theta extra : E)
    (split : whole = homogeneous + force + toroidal)
    (tor : div toroidal = axial (axial theta + extra)) :
    div whole = div homogeneous + div force + axial (axial theta) + axial extra := by
  rw [split, map_add, map_add, tor, map_add]
  abel

theorem actualReconstruction_div_split (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell) :
    apSmoothDiv admissible (compensatedReconstruct admissible (reconstructedState admissible theta source)) =
      apSmoothDiv admissible (homogeneousLift admissible theta source) +
        apSmoothDiv admissible (forceLift admissible source.1) +
        apSmoothAxial L sigma gamma ell 1 (apSmoothAxial L sigma gamma ell 1 theta) +
        apSmoothAxial L sigma gamma ell 1 (reconstructedScalar admissible source.2.2) :=
  div_split_algebra (apSmoothDiv admissible) (apSmoothAxial L sigma gamma ell 1)
    _ _ _ _ theta (reconstructedScalar admissible source.2.2)
    (actualReconstruction_split admissible theta source) (div_toroidalLift admissible _)

end Grad.ActualScalarForcing
