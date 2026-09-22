import ANK2ActualDivergenceCovariance

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualScalarResidual
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.RawCircularSectors Grad.ActualNonexceptionalInverse Grad.ActualAngularInverse
variable {L sigma gamma ell : ℝ}

theorem reconstructedScalar_excluded (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (excluded : AvoidsExceptionalSource source)
    (mode : ℤ) (exceptional : IsExceptionalRaw mode) :
    apSmoothAngularMode L sigma gamma ell 1 mode (reconstructedScalar admissible source.2.2) = 0 := by
  apply apSmoothJet_ext admissible
  intro cell
  have absent := (rawSource_excluded_components admissible mode source (excluded mode exceptional) cell).2.2
  have inverseAbsent : angularClosedJet mode (shiftInverseJet 0 (apSmoothJet admissible 1 cell source.2.2)) = 0 :=
    (shiftInverseJet_angular 0 mode _).symm.trans
      ((congrArg (shiftInverseJet 0) absent).trans (map_zero (shiftInverseLinear 1 0)))
  have actual := (congrArg (angularClosedJet mode) (apShiftInverse_jet admissible 0 source.2.2 cell)).trans inverseAbsent
  exact (apSmoothAngularMode_jet admissible mode (reconstructedScalar admissible source.2.2) cell).trans
    (actual.trans (map_zero (apSmoothJet admissible 1 cell)).symm)

theorem rawStored_zero_of_components (mode : ℤ) (field : APSmooth L sigma gamma ell 3)
    (planar : apSmoothRawVector L sigma gamma ell mode (apSmoothPlanar L sigma gamma ell field) = 0)
    (scalar : apSmoothAngularMode L sigma gamma ell 1 mode (apSmoothScalar L sigma gamma ell field) = 0) :
    apSmoothRawStored L sigma gamma ell mode field = 0 := by
  have first := (congrArg (apSmoothValueMap L sigma gamma ell planarInclusionMap) planar).trans
    (map_zero (apSmoothValueMap L sigma gamma ell planarInclusionMap))
  have second := (congrArg (apSmoothValueMap L sigma gamma ell toroidalInclusionMap) scalar).trans
    (map_zero (apSmoothValueMap L sigma gamma ell toroidalInclusionMap))
  exact (congrArg₂ (fun a b : APSmooth L sigma gamma ell 3 => a + b) first second).trans (zero_add _)

/-- The explicit ANV state itself belongs to the actual raw complement; this is
proved from its source and scalar input, rather than imposed on the state. -/
theorem reconstructedState_excluded (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source) :
    AvoidsExceptionalState (reconstructedState admissible theta source) := by
  intro mode exceptional
  have scalar := reconstructedScalar_excluded admissible source sourceExcluded mode exceptional
  have vector := reconstructedVector_excluded admissible theta source thetaExcluded sourceExcluded mode exceptional
  have projectedPlanar := (congrArg (apSmoothRawVector L sigma gamma ell mode)
    (reconstructedState_planar admissible theta source)).trans vector
  have projectedScalar := (congrArg (apSmoothAngularMode L sigma gamma ell 1 mode)
    (reconstructedState_scalar admissible theta source)).trans scalar
  have stored := rawStored_zero_of_components mode (reconstructedState admissible theta source).2 projectedPlanar projectedScalar
  apply Prod.ext
  · exact scalarAvoids_projector_zero admissible theta thetaExcluded mode exceptional
  · exact stored

theorem reconstructedState_divergence_excluded (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source) :
    ScalarAvoidsExceptional admissible
      (apSmoothDiv admissible (compensatedReconstruct admissible (reconstructedState admissible theta source))) :=
  state_divergence_excluded admissible _ (reconstructedState_excluded admissible theta source thetaExcluded sourceExcluded)

theorem source_scalar_excluded (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (excluded : AvoidsExceptionalSource source) :
    ScalarAvoidsExceptional admissible source.2.1 :=
  fun cell mode exceptional => (rawSource_excluded_components admissible mode source (excluded mode exceptional) cell).2.1

theorem scalarExcluded_add (admissible : Admissible L sigma gamma ell)
    (first second : APSmooth L sigma gamma ell 1)
    (firstExcluded : ScalarAvoidsExceptional admissible first) (secondExcluded : ScalarAvoidsExceptional admissible second) :
    ScalarAvoidsExceptional admissible (first + second) := by
  intro cell mode exceptional
  rw [map_add, angularClosedJet_add, firstExcluded cell mode exceptional, secondExcluded cell mode exceptional, add_zero]

theorem reconstructedResidual_excluded (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source) :
    ScalarAvoidsExceptional admissible
      (apSmoothDiv admissible (compensatedReconstruct admissible (reconstructedState admissible theta source)) + source.2.1) :=
  scalarExcluded_add admissible _ _
    (reconstructedState_divergence_excluded admissible theta source thetaExcluded sourceExcluded)
    (source_scalar_excluded admissible source sourceExcluded)

end Grad.ActualScalarResidual
