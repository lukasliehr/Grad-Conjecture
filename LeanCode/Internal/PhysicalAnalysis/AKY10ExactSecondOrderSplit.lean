import AKY9ProjectedActualFlux

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.CartesianUncompressed
open Grad.ClosedJets Grad.Constraints
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.CartesianScalarElimination Grad.CircularHighRegularity Grad.NonlinearDivision Grad.NonlinearRange

def radialMeanSourceLinear : ClosedJet 2 →ₗ[ℂ] ClosedJet 2 :=
  (1 / 2 : ℂ) • (valueMapJetLinear 2 2 quarterValueMap).comp equivariantAverageLinear

/-- ER11: the two-planar-derivative terms, with s=h_perp−JAa/2. -/
def erPlanarPrincipal (correction forceCorrection : ClosedJet 2) : ClosedJet 2 :=
  hodgeDivergenceLinear (vectorDivLinear (correction - radialMeanSourceLinear forceCorrection)) +
    curlPrimitiveGradient forceCorrection

def erScalarPrincipal (correction : ClosedJet 1) : ClosedJet 1 :=
  scalarAngularInverse (laplacianJetLinear correction)

/-- ER12: exactly one cell derivative, and no Theta. -/
def erPlanarMixed (frequency : ℂ) (scalar correction : ClosedJet 1) : ClosedJet 2 :=
  hodgeDivergenceLinear (frequency • (-scalar + correction))

def erScalarMixed (frequency : ℂ) (vector forceCorrection : ClosedJet 2) : ClosedJet 1 :=
  frequency • vectorDivLinear (recoveredGradientLinear vector - covariantAngularInverse forceCorrection)

/-- ER13: fixed sources only, retaining the radial vector source projection. -/
def erPlanarSource (force : ClosedJet 2) (source : ClosedJet 1) : ClosedJet 2 :=
  -hodgeDivergenceLinear source + hodgeDivergenceLinear (vectorDivLinear (radialMeanSourceLinear force)) -
    curlPrimitiveGradient force

def erScalarSource (frequency : ℂ) (force : ClosedJet 2) (source : ClosedJet 1) : ClosedJet 1 :=
  frequency • vectorDivLinear (covariantAngularInverse force) + scalarAngularInverse (laplacianJetLinear source)

theorem planar_secondOrder_split (frequency : ℂ) (vector force forceCorrection correction : ClosedJet 2)
    (scalar scalarCorrection source : ClosedJet 1)
    (divergence : vectorDivLinear vector = -source + frequency • (-scalar + scalarCorrection) +
      vectorDivLinear (correction + radialMeanSourceLinear (force - forceCorrection))) :
    hodgeDivergenceLinear (vectorDivLinear vector) + curlPrimitiveGradient (forceCorrection - force) =
      erPlanarPrincipal correction forceCorrection + erPlanarMixed frequency scalar scalarCorrection +
        erPlanarSource force source := by
  rw [divergence]
  simp only [erPlanarPrincipal, erPlanarMixed, erPlanarSource, map_add, map_sub, map_neg]
  module

theorem scalar_secondOrder_split (frequency : ℂ) (vector force forceCorrection : ClosedJet 2)
    (source correction : ClosedJet 1) :
    frequency • vectorDivLinear (recoveredGradientLinear vector + covariantAngularInverse (force - forceCorrection)) +
      scalarAngularInverse (laplacianJetLinear (source + correction)) =
        erScalarPrincipal correction + erScalarMixed frequency vector forceCorrection +
          erScalarSource frequency force source := by
  simp only [erScalarPrincipal, erScalarMixed, erScalarSource, map_add, map_sub, smul_add, smul_sub]
  module

/-- The exact ER10–13 second-order system, derived from the actual first-order
Cartesian equations and their two original gauges. The right sides have no
Theta and at most one factor of the cell frequency in mixed and source terms. -/
theorem uncompressed_secondOrder_system (frequency : ℂ) (theta scalar source third scalarCorrection thirdCorrection : ClosedJet 1)
    (vector force forceCorrection correction : ClosedJet 2)
    (thetaMean : angularClosedJet 0 theta = 0) (scalarMean : angularClosedJet 0 scalar = 0)
    (tangentialGauge : tangentialJet vector = 0)
    (correctionMean : angularClosedJet 0 scalarCorrection = 0)
    (vectorCorrectionMean : equivariantAverageJet correction = 0)
    (forceRow : force - forceCorrection = gradientJet (rotationJet theta) -
      (rotationJet vector + valueMapJet quarterValueMap vector))
    (thirdRow : third + thirdCorrection = rotationJet (scalar - frequency • theta))
    (determinantRow : source = scalarMeanFreeLinear
      (-vectorDivJet vector - frequency • scalar + vectorDivJet correction + frequency • scalarCorrection)) :
    planarLaplacian 2 vector = erPlanarPrincipal correction forceCorrection +
      erPlanarMixed frequency scalar scalarCorrection + erPlanarSource force source ∧
    laplacianJet scalar = erScalarPrincipal thirdCorrection +
      erScalarMixed frequency vector forceCorrection + erScalarSource frequency force third := by
  have divergence := actual_divergence_recovery frequency vector correction scalar scalarCorrection source
    scalarMean correctionMean vectorCorrectionMean determinantRow
  have mean := actual_radial_mean_recovery theta vector force forceCorrection forceRow
  change equivariantAverageJet vector = radialMeanSourceLinear (force - forceCorrection) at mean
  rw [mean] at divergence
  constructor
  · exact (actual_planar_elimination theta vector force forceCorrection tangentialGauge forceRow).trans
      (planar_secondOrder_split frequency vector force forceCorrection correction scalar scalarCorrection source divergence)
  · exact (actual_scalar_elimination frequency theta scalar third thirdCorrection vector force forceCorrection
      thetaMean scalarMean forceRow thirdRow).trans (scalar_secondOrder_split frequency vector force forceCorrection third thirdCorrection)

end Grad.CartesianUncompressed
