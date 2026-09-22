import ANV11VectorModeCommutation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualNonexceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.ActualAngularInverse
open Grad.RawCircularSectors
variable {L sigma gamma ell : ℝ}

theorem rawMeanZero_tangential_zero (field : ClosedJet 2) (excluded : rawVectorJet 0 field = 0) :
    tangentialJet field = 0 := by
  have mean : equivariantAverageJet field = 0 := (rawVectorJet_zero field).symm.trans excluded
  rw [tangentialJet_eq, mean]
  change (1 / 2 : ℂ) • (0 - reflectedVectorLinear 0) = 0
  rw [map_zero, sub_self, smul_zero]

theorem reconstructedVector_tangential_zero (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source) :
    apSmoothTangential L sigma gamma ell (reconstructedVector admissible theta source.1) = 0 := by
  have projected := reconstructedVector_excluded admissible theta source thetaExcluded sourceExcluded 0 (Or.inl rfl)
  apply apSmoothJet_ext admissible
  intro cell
  have rawZero := (apSmoothRawVector_jet admissible 0 _ cell).symm.trans
    ((congrArg (apSmoothJet admissible 2 cell) projected).trans (map_zero _))
  exact (apSmoothTangential_jet admissible _ cell).trans
    ((rawMeanZero_tangential_zero _ rawZero).trans (map_zero _).symm)

theorem reconstructedScalar_mean_zero (admissible : Admissible L sigma gamma ell)
    (source : APSmooth L sigma gamma ell 1) :
    apSmoothAngularMean L sigma gamma ell 1 (reconstructedScalar admissible source) = 0 := by
  apply apSmoothJet_ext admissible
  intro cell
  have nonresonant := apShiftInverse_nonresonant admissible 0 source cell
  have zero : angularClosedJet 0 (apSmoothJet admissible 1 cell (reconstructedScalar admissible source)) = 0 := by
    simpa only [reconstructedScalar, neg_zero] using nonresonant
  exact (apSmoothAngularMean_jet admissible _ cell).trans (zero.trans (map_zero _).symm)

theorem storedPair_complement_zero (admissible : Admissible L sigma gamma ell)
    (vector : APSmooth L sigma gamma ell 2) (scalar : APSmooth L sigma gamma ell 1)
    (vectorGauge : apSmoothTangential L sigma gamma ell vector = 0)
    (scalarGauge : apSmoothAngularMean L sigma gamma ell 1 scalar = 0) :
    apSmoothComplement L sigma gamma ell (storedPair L sigma gamma ell vector scalar) = 0 := by
  let stored := storedPair L sigma gamma ell vector scalar
  let projected := apSmoothComplement L sigma gamma ell stored
  have planar := (apSmoothPlanar_complement admissible stored).trans
    ((congrArg (apSmoothTangential L sigma gamma ell) (storedPair_planar admissible vector scalar)).trans vectorGauge)
  have toroidal := (apSmoothScalar_complement admissible stored).trans
    ((congrArg (apSmoothAngularMean L sigma gamma ell 1) (storedPair_scalar admissible vector scalar)).trans scalarGauge)
  have first := (congrArg (apSmoothValueMap L sigma gamma ell planarInclusionMap) planar).trans (map_zero _)
  have second := (congrArg (apSmoothValueMap L sigma gamma ell toroidalInclusionMap) toroidal).trans (map_zero _)
  exact (apSmooth_splitting admissible projected).symm.trans
    ((congrArg₂ (fun a b : APSmooth L sigma gamma ell 3 => a + b) first second).trans (zero_add _))

theorem reconstructedState_complement_zero (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source) :
    apSmoothComplement L sigma gamma ell (compensatedReconstruct admissible (reconstructedState admissible theta source)) = 0 := by
  have gradient := apSmoothCovariant_complement_zero admissible theta (fun cell => thetaExcluded cell 0 (Or.inl rfl))
  have stored := storedPair_complement_zero admissible _ _
    (reconstructedVector_tangential_zero admissible theta source thetaExcluded sourceExcluded)
    (reconstructedScalar_mean_zero admissible source.2.2)
  exact (map_add (apSmoothComplement L sigma gamma ell) _ _).trans
    ((congrArg₂ (fun a b : APSmooth L sigma gamma ell 3 => a + b) gradient stored).trans (zero_add _))

/-- Literal membership in the accepted circular compensated domain: both
original gauges and the reconstructed Cartesian first jet are proved. -/
theorem reconstructedState_circularCore (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source)
    (thetaFlat : APSmoothAxisFirstJetZero admissible theta) :
    reconstructedState admissible theta source ∈ circularCompensatedCore admissible :=
  ⟨reconstructedState_flatCore admissible theta source compatible thetaExcluded sourceExcluded thetaFlat,
    reconstructedState_complement_zero admissible theta source thetaExcluded sourceExcluded⟩

end Grad.ActualNonexceptionalInverse
