import AKY4ActualZeroOrderRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.CartesianUncompressed
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.ActualAngularInverse Grad.RawCircularSectors Grad.CartesianScalarElimination
open Grad.CircularHighRegularity
open Grad.CircularHighWeak Grad.NonlinearDivision Grad.NonlinearRange

/-- ER5's literal grad−2JgradK operator. -/
def hodgeDivergenceLinear : ClosedJet 1 →ₗ[ℂ] ClosedJet 2 :=
  cartesianGradient - (2 : ℂ) • (valueMapJetLinear 2 2 quarterValueMap).comp
    (cartesianGradient.comp scalarAngularInverse)

def curlPrimitiveGradient : ClosedJet 2 →ₗ[ℂ] ClosedJet 2 :=
  (valueMapJetLinear 2 2 quarterValueMap).comp
    (cartesianGradient.comp (scalarAngularInverse.comp planarCurlLinear))

theorem actual_planar_elimination (theta : ClosedJet 1) (vector force correction : ClosedJet 2)
    (gauge : tangentialJet vector = 0)
    (forceRow : force - correction = gradientJet (rotationJet theta) -
      (rotationJet vector + valueMapJet quarterValueMap vector)) :
    planarLaplacian 2 vector = hodgeDivergenceLinear (vectorDivJet vector) +
      curlPrimitiveGradient (correction - force) := by
  rw [cartesian_hodge, actual_curl_recovery theta vector force correction gauge forceRow]
  rw [map_sub, map_smul]
  have grad := cartesianGradient.map_sub
    (scalarAngularInverse (planarCurlJet (correction - force)))
    ((2 : ℂ) • scalarAngularInverse (vectorDivJet vector))
  change gradientJet (_ - _) = gradientJet _ - gradientJet _ at grad
  rw [grad]
  change _ + (valueMapJetLinear 2 2 quarterValueMap) (_ - _) = _
  rw [map_sub]
  have scaled := cartesianGradient.map_smul (2 : ℂ) (scalarAngularInverse (vectorDivJet vector))
  change gradientJet ((2 : ℂ) • _) = (2 : ℂ) • gradientJet _ at scaled
  rw [scaled, map_smul]
  change gradientJet (vectorDivJet vector) +
    (valueMapJet quarterValueMap (gradientJet (scalarAngularInverse (planarCurlJet (correction - force)))) -
      (2 : ℂ) • valueMapJet quarterValueMap (gradientJet (scalarAngularInverse (vectorDivJet vector)))) =
    (gradientJet (vectorDivJet vector) -
    (2 : ℂ) • valueMapJet quarterValueMap (gradientJet (scalarAngularInverse (vectorDivJet vector)))) +
      valueMapJet quarterValueMap (gradientJet (scalarAngularInverse (planarCurlJet (correction - force))))
  module

theorem actual_scalar_elimination (frequency : ℂ) (theta scalar source correction : ClosedJet 1)
    (vector force planarCorrection : ClosedJet 2)
    (thetaMean : angularClosedJet 0 theta = 0) (scalarMean : angularClosedJet 0 scalar = 0)
    (forceRow : force - planarCorrection = gradientJet (rotationJet theta) -
      (rotationJet vector + valueMapJet quarterValueMap vector))
    (thirdRow : source + correction = rotationJet (scalar - frequency • theta)) :
    laplacianJet scalar = frequency • vectorDivJet
      (recoveredGradientLinear vector + covariantAngularInverse (force - planarCorrection)) +
        scalarAngularInverse (laplacianJet (source + correction)) := by
  have recovered :=  actual_scalar_recovery frequency theta scalar source correction thetaMean scalarMean thirdRow
  have differentiated := congrArg laplacianJetLinear recovered
  rw [map_add, map_smul] at differentiated
  change laplacianJet scalar = frequency • laplacianJet theta +
    laplacianJet (scalarAngularInverse (source + correction)) at differentiated
  rw [← scalarAngularInverse_laplacian] at differentiated
  have gradient := actual_gradient_recovery theta vector force planarCorrection thetaMean forceRow
  have divergence := congrArg vectorDivLinear gradient
  change vectorDivJet (gradientJet theta) = _ at divergence
  rw [vectorDivJet_gradient] at divergence
  exact differentiated.trans (congrArg (fun value : ClosedJet 1 =>
    frequency • value + scalarAngularInverse (laplacianJet (source + correction))) divergence)

/-- Restore precisely the removed scalar angular mean in the determinant row.
The actual equivariant vector mean is retained as its divergence. -/
theorem actual_divergence_recovery (frequency : ℂ) (vector correction : ClosedJet 2)
    (scalar scalarCorrection source : ClosedJet 1)
    (scalarMean : angularClosedJet 0 scalar = 0)
    (correctionMean : angularClosedJet 0 scalarCorrection = 0)
    (vectorMean : equivariantAverageJet correction = 0)
    (determinantRow : source =
      (-vectorDivJet vector - frequency • scalar + vectorDivJet correction + frequency • scalarCorrection) -
        angularClosedJet 0
          (-vectorDivJet vector - frequency • scalar + vectorDivJet correction + frequency • scalarCorrection)) :
    vectorDivJet vector = -source + frequency • (-scalar + scalarCorrection) +
      vectorDivJet (correction + equivariantAverageJet vector) := by
  have zeroDiv : angularClosedJet 0 (vectorDivJet correction) = 0 := by
    rw [← average_div, vectorMean]
    exact map_zero vectorDivLinear
  have row := determinantRow
  rw [angularClosedJet_add, angularClosedJet_add, angularClosedJet_sub_actual,
    angularClosedJet_smul, angularClosedJet_smul, scalarMean, correctionMean, zeroDiv,
    smul_zero] at row
  simp only [add_zero, sub_zero] at row
  have negMean : angularClosedJet 0 (-vectorDivJet vector) =
      -angularClosedJet 0 (vectorDivJet vector) := map_neg (angularClosedJetLinear 1 0) _
  rw [negMean, ← average_div] at row
  change _ = _ + vectorDivLinear (_ + _)
  rw [map_add, smul_add, smul_neg, row]
  simp only [vectorDivJet]
  module

end Grad.CartesianUncompressed
