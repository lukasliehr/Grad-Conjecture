import AKY3CartesianMeanAndHodge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.CartesianUncompressed
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.ActualAngularInverse Grad.RawCircularSectors Grad.CartesianScalarElimination
open Grad.CircularHighRegularity
open Grad.ActualScalarForcing Grad.CircularHighWeak Grad.NonlinearDivision Grad.NonlinearRange

def scalarAngularInverse : ClosedJet 1 →ₗ[ℂ] ClosedJet 1 := shiftInverseLinear 1 0

theorem angularClosedJet_sub_actual {dimension : ℕ} (mode : ℤ)
    (first second : ClosedJet dimension) : angularClosedJet mode (first - second) =
      angularClosedJet mode first - angularClosedJet mode second :=
  map_sub (angularClosedJetLinear dimension mode) first second

def recoveredGradientLinear : ClosedJet 2 →ₗ[ℂ] ClosedJet 2 :=
  (LinearMap.id - rawVectorJetLinear 0) +
    (2 : ℂ) • covariantAngularInverse.comp (valueMapJetLinear 2 2 quarterValueMap)

theorem scalarAngularInverse_rotation (field : ClosedJet 1) :
    scalarAngularInverse (rotationJet field) = field - angularClosedJet 0 field := by
  change shiftInverseJet 0 (rotationJet field) = _
  have law := shiftInverse_left 0 field
  rw [excluded_single_eq] at law
  simpa only [shiftedRotationJet, Int.cast_zero, mul_zero, zero_smul, add_zero,
    neg_zero] using law

theorem scalarAngularInverse_laplacian (field : ClosedJet 1) :
    scalarAngularInverse (laplacianJet field) = laplacianJet (scalarAngularInverse field) := by
  apply scalarJet_angular_ext
  intro mode
  change angularClosedJet mode (shiftInverseJet 0 (laplacianJet field)) =
    angularClosedJet mode (laplacianJet (shiftInverseJet 0 field))
  rw [← laplacianJet_angular mode (shiftInverseJet 0 field), shiftInverseJet_coefficient,
    shiftInverseJet_coefficient]
  split_ifs with resonant
  · exact (map_zero laplacianJetLinear).symm
  · rw [← laplacianJet_angular]
    exact (map_smul laplacianJetLinear _ _).symm

/-- ER4's radial equivariant part is recovered and is not set to zero. -/
theorem actual_radial_mean_recovery (theta : ClosedJet 1) (vector force correction : ClosedJet 2)
    (forceRow : force - correction = gradientJet (rotationJet theta) -
      (rotationJet vector + valueMapJet quarterValueMap vector)) :
    equivariantAverageJet vector = (1 / 2 : ℂ) •
      valueMapJet quarterValueMap (equivariantAverageJet (force - correction)) := by
  have meanRot : angularClosedJet 0 (rotationJet theta) = 0 := by
    rw [angular_rotationJet_all]
    simp
  have zero := average_gradient_zero (rotationJet theta) meanRot
  have meanLaw := congrArg (rawVectorJetLinear 0) forceRow
  change equivariantAverageJet (force - correction) =
    equivariantAverageJet (gradientJet (rotationJet theta) -
      (rotationJet vector + valueMapJet quarterValueMap vector)) at meanLaw
  rw [equivariantAverageJet_sub (gradientJet (rotationJet theta))
    (rotationJet vector + valueMapJet quarterValueMap vector)] at meanLaw
  have splitAverage : equivariantAverageJet (rotationJet vector + valueMapJet quarterValueMap vector) =
      equivariantAverageJet (rotationJet vector) + equivariantAverageJet (valueMapJet quarterValueMap vector) :=
    map_add (rawVectorJetLinear 0) _ _
  rw [zero, splitAverage, average_rotation, averageJet_quarter] at meanLaw
  rw [meanLaw]
  change _ = (1 / 2 : ℂ) • (valueMapJetLinear 2 2 quarterValueMap) (0 - (_ + _))
  rw [map_sub, map_zero, map_add]
  change _ = (1 / 2 : ℂ) • (0 - (valueMapJet quarterValueMap (valueMapJet quarterValueMap _) +
    valueMapJet quarterValueMap (valueMapJet quarterValueMap _)))
  rw [quarterJet_square]
  module

/-- Exact order-zero recovery of the actual gradient; no scalar unknown remains
on the right and no exceptional angular mode has been discarded. -/
theorem actual_gradient_recovery (theta : ClosedJet 1) (vector force correction : ClosedJet 2)
    (mean : angularClosedJet 0 theta = 0)
    (forceRow : force - correction = gradientJet (rotationJet theta) -
      (rotationJet vector + valueMapJet quarterValueMap vector)) :
    gradientJet theta = recoveredGradientLinear vector + covariantAngularInverse (force - correction) := by
  have inverse := covariantAngularInverse_left (gradientJet theta)
  rw [average_gradient_zero theta mean, sub_zero] at inverse
  have rotated := rotation_gradient_actual theta
  have input : rotationJet (gradientJet theta) - valueMapJet quarterValueMap (gradientJet theta) =
      (rotationJet vector - valueMapJet quarterValueMap vector) +
        (2 : ℂ) • valueMapJet quarterValueMap vector + (force - correction) := by
    rw [rotated, forceRow]
    module
  rw [input, map_add, map_add, map_smul, covariantAngularInverse_left] at inverse
  exact inverse.symm

/-- The scalar row recovers the same b from DTheta and the actual known and
coefficient terms; the scalar mean is the only removed mode. -/
theorem actual_scalar_recovery (frequency : ℂ) (theta scalar source correction : ClosedJet 1)
    (thetaMean : angularClosedJet 0 theta = 0) (scalarMean : angularClosedJet 0 scalar = 0)
    (thirdRow : source + correction = rotationJet (scalar - frequency • theta)) :
    scalar = frequency • theta + scalarAngularInverse (source + correction) := by
  have inverse := congrArg scalarAngularInverse thirdRow
  rw [scalarAngularInverse_rotation, angularClosedJet_sub_actual, angularClosedJet_smul,
    scalarMean, thetaMean, smul_zero, sub_zero, sub_zero] at inverse
  rw [inverse]
  module

/-- Curl of the actual force row and the fixed tangential gauge give the
uncompressed scalar K formula in ER4. -/
theorem actual_curl_recovery (theta : ClosedJet 1) (vector force correction : ClosedJet 2)
    (gauge : tangentialJet vector = 0)
    (forceRow : force - correction = gradientJet (rotationJet theta) -
      (rotationJet vector + valueMapJet quarterValueMap vector)) :
    planarCurlJet vector = scalarAngularInverse
      (planarCurlJet (correction - force) - (2 : ℂ) • vectorDivJet vector) := by
  have curls := congrArg planarCurlLinear forceRow
  change planarCurlLinear (force - correction) = planarCurlLinear
    (gradientJet (rotationJet theta) - (rotationJet vector + valueMapJet quarterValueMap vector)) at curls
  rw [map_sub, map_sub] at curls
  change planarCurlJet force - planarCurlJet correction =
    planarCurlJet (gradientJet (rotationJet theta)) -
      planarCurlJet (rotationJet vector + valueMapJet quarterValueMap vector) at curls
  rw [planarCurlJet_gradient, planarCurlJet_rotationPlusQuarter] at curls
  have negative := congrArg Neg.neg curls
  simp only [neg_sub, sub_zero] at negative
  have row : rotationJet (planarCurlJet vector) =
      planarCurlJet (correction - force) - (2 : ℂ) • vectorDivJet vector := by
    change rotationJet (planarCurlJet vector) = planarCurlLinear (_ - _) - _
    rw [map_sub]
    change rotationJet (planarCurlJet vector) =
      (planarCurlJet correction - planarCurlJet force) - _
    rw [negative]
    module
  have inverse := congrArg scalarAngularInverse row
  rw [scalarAngularInverse_rotation, curl_mean_zero_of_tangential_zero vector gauge,
    sub_zero] at inverse
  exact inverse

end Grad.CartesianUncompressed
