import ANF5ActualHomogeneousVelocity
import ANT6ActualClosedDiskConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualScalarForcing
open Grad.NonlinearDivision Grad.GaugeCoefficients.Physical.Frame
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.ActualAngularInverse Grad.ActualNonexceptionalInverse Grad.RawCircularSectors
open Grad.CartesianScalarElimination Grad.CircularHighRegularity Grad.CircularHighWeak
variable {L sigma gamma ell : ℝ}

def homogeneousLift (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell) : APSmooth L sigma gamma ell 3 :=
  apSmoothValueMap L sigma gamma ell planarInclusionMap (homogeneousVelocity admissible theta source)

theorem homogeneousVelocity_jet_equation (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source)
    (cell : ℤ) :
    rotationJet (apSmoothJet admissible 2 cell (homogeneousVelocity admissible theta source)) +
      valueMapJet quarterValueMap (apSmoothJet admissible 2 cell (homogeneousVelocity admissible theta source)) =
        gradientJet (rotationJet (apSmoothJet admissible 1 cell theta)) := by
  let jet := apSmoothJet admissible 2 cell
  let velocity := homogeneousVelocity admissible theta source
  have left := (jet.map_add (apSmoothRotation admissible 2 velocity) (apSmoothQuarter L sigma gamma ell velocity)).trans
    (congrArg₂ (fun a b : ClosedJet 2 => a + b) (apSmoothRotation_jet admissible velocity cell)
      (apSmoothValueMap_jet admissible quarterValueMap velocity cell))
  have right := (apSmoothGradient_jet admissible (apSmoothRotation admissible 1 theta) cell).trans
    (congrArg gradientJet (apSmoothRotation_jet admissible theta cell))
  exact left.symm.trans ((congrArg jet (homogeneousVelocity_equation admissible theta source thetaExcluded sourceExcluded)).trans right)

theorem div_planarLift_jet (admissible : Admissible L sigma gamma ell)
    (vector : APSmooth L sigma gamma ell 2) (cell : ℤ) :
    apSmoothJet admissible 1 cell (apSmoothDiv admissible (apSmoothValueMap L sigma gamma ell planarInclusionMap vector)) =
      planarDivJet (valueMapJet planarInclusionMap (apSmoothJet admissible 2 cell vector)) := by
  have image := apSmoothValueMap_jet admissible planarInclusionMap vector cell
  have toroidal : valueMapJet toroidalPartMap (valueMapJet planarInclusionMap (apSmoothJet admissible 2 cell vector)) = 0 := by
    rw [valueMapJet_comp, toroidalPart_planarInclusion, valueMapJet_zero]
  have zero := (congrArg (valueMapJet toroidalPartMap) image).trans toroidal
  exact (apSmoothDiv_jet admissible _ cell).trans
    ((congrArg₂ (fun a b : ClosedJet 1 => a + seedScaledFrequency L ell cell • b)
      (congrArg planarDivJet image) zero).trans (by rw [smul_zero, add_zero]))

theorem radial_planarLift_jet (admissible : Admissible L sigma gamma ell)
    (vector : APSmooth L sigma gamma ell 2) (cell : ℤ) :
    apSmoothJet admissible 1 cell (apSmoothRadial admissible (apSmoothValueMap L sigma gamma ell planarInclusionMap vector)) =
      apProductJet radialRowJet (valueMapJet planarInclusionMap (apSmoothJet admissible 2 cell vector)) :=
  (apSmoothFixedJet_jet admissible radialRowJet _ cell).trans
    (congrArg (apProductJet radialRowJet) (apSmoothValueMap_jet admissible planarInclusionMap vector cell))

/-- AN14 now applied to the actual reconstructed AP velocity, with the full
multiplier and both original physical contractions faithfully realized. -/
theorem actualReconstructedElimination (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source)
    (cell : ℤ) :
    apSmoothJet admissible 1 cell (apFullB admissible (apSmoothDiv admissible (homogeneousLift admissible theta source))) =
      laplacianJet (apSmoothJet admissible 1 cell theta) ∧
    apSmoothJet admissible 1 cell (apFullB admissible (apSmoothRadial admissible (homogeneousLift admissible theta source))) =
      eulerJet (apSmoothJet admissible 1 cell theta) + (2 : ℂ) • apSmoothJet admissible 1 cell theta := by
  have actual := actualHomogeneousScalarElimination (apSmoothJet admissible 1 cell theta)
    (apSmoothJet admissible 2 cell (homogeneousVelocity admissible theta source))
    (thetaExcluded cell 0 (by simp [IsExceptionalRaw]))
    (homogeneousVelocity_jet_equation admissible theta source thetaExcluded sourceExcluded cell)
  have divJet := div_planarLift_jet admissible (homogeneousVelocity admissible theta source) cell
  have radialJet := radial_planarLift_jet admissible (homogeneousVelocity admissible theta source) cell
  constructor
  · exact (apFullB_jet admissible _ cell).trans
      ((congrArg (fun jet : ClosedJet 1 => jet + (4 : ℂ) • shiftInverseJet 0 (shiftInverseJet 0 jet)) divJet).trans actual.1)
  · exact (apFullB_jet admissible _ cell).trans
      ((congrArg (fun jet : ClosedJet 1 => jet + (4 : ℂ) • shiftInverseJet 0 (shiftInverseJet 0 jet)) radialJet).trans actual.2)

end Grad.ActualScalarForcing
