import AKY2TrueCovariantAngularInverse
import ANF5ActualHomogeneousVelocity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.CartesianUncompressed
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.ActualAngularInverse Grad.ActualNonexceptionalInverse Grad.RawCircularSectors
open Grad.CartesianScalarElimination Grad.ActualScalarForcing Grad.ActualMeanInverse
open Grad.GaugeCoefficients.Physical.Ledger
open Grad.CircularHighWeak Grad.NonlinearDivision Grad.NonlinearRange

def cartesianGradient : ClosedJet 1 →ₗ[ℂ] ClosedJet 2 :=
  (valueMapJetLinear 1 2 (matrixUnit 0 0)).comp (partialJetLinear 1 0) +
    (valueMapJetLinear 1 2 (matrixUnit 1 0)).comp (partialJetLinear 1 1)

theorem cartesianGradient_eq (field : ClosedJet 1) : cartesianGradient field = gradientJet field := rfl

def planarLaplacian (dimension : ℕ) : ClosedJet dimension →ₗ[ℂ] ClosedJet dimension :=
  (partialJetLinear dimension 0).comp (partialJetLinear dimension 0) +
    (partialJetLinear dimension 1).comp (partialJetLinear dimension 1)

theorem planarLaplacian_scalar (field : ClosedJet 1) :
    planarLaplacian 1 field = laplacianJet field := rfl

theorem average_gradient (field : ClosedJet 1) :
    equivariantAverageJet (gradientJet field) = gradientJet (angularClosedJet 0 field) :=
  (rawVectorJet_zero _).symm.trans (gradientJet_angular 0 field).symm

theorem average_gradient_zero (field : ClosedJet 1) (mean : angularClosedJet 0 field = 0) :
    equivariantAverageJet (gradientJet field) = 0 := by
  rw [average_gradient, mean]
  exact map_zero cartesianGradient

theorem average_curl (field : ClosedJet 2) :
    planarCurlJet (equivariantAverageJet field) = angularClosedJet 0 (planarCurlJet field) :=
  (congrArg planarCurlJet (rawVectorJet_zero field).symm).trans (planarCurlJet_rawVector 0 field)

theorem average_div (field : ClosedJet 2) :
    vectorDivJet (equivariantAverageJet field) = angularClosedJet 0 (vectorDivJet field) := by
  change planarCurlJet (valueMapJet quarterValueMap (equivariantAverageJet field)) = _
  rw [← averageJet_quarter, average_curl]
  rfl

theorem average_rotation (field : ClosedJet 2) :
    equivariantAverageJet (rotationJet field) =
      valueMapJet quarterValueMap (equivariantAverageJet field) := by
  have fixed := equivariantAverageJet_idempotent field
  rw [← rawVectorJet_zero, ← rotationJet_rawVector, rawVectorJet_zero]
  exact rotationJet_of_equivariant _ fixed

/-- The fixed tangential gauge leaves the radial equivariant vector. -/
theorem average_of_tangential_zero (field : ClosedJet 2) (gauge : tangentialJet field = 0) :
    equivariantAverageJet field =
      -valueMapJet quarterValueMap (tangentialJet (valueMapJet quarterValueMap field)) := by
  have first := quarter_tangential_quarter field
  have second : (1 / 2 : ℂ) •
      (equivariantAverageJet field - reflectedVectorJet (equivariantAverageJet field)) = 0 :=
    (tangentialJet_eq field).symm.trans gauge
  rw [first]
  calc
    _ = (1 / 2 : ℂ) • (equivariantAverageJet field -
        reflectedVectorJet (equivariantAverageJet field)) +
          (1 / 2 : ℂ) • (equivariantAverageJet field +
            reflectedVectorJet (equivariantAverageJet field)) := by module
    _ = _ := by rw [second]; module

theorem curl_mean_zero_of_tangential_zero (field : ClosedJet 2)
    (gauge : tangentialJet field = 0) : angularClosedJet 0 (planarCurlJet field) = 0 := by
  rw [← average_curl, average_of_tangential_zero field gauge]
  change planarCurlLinear (-_) = 0
  rw [map_neg]
  change -planarCurlJet (valueMapJet quarterValueMap (tangentialJet _)) = 0
  rw [planarCurlJet_quarter_tangential, neg_zero]

theorem vectorDivJet_explicit (field : ClosedJet 2) :
    vectorDivJet field = valueMapJet (matrixUnit 0 0) (partialJet 0 field) +
      valueMapJet (matrixUnit 0 1) (partialJet 1 field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  change (vectorDivJet field).value point 0 = _
  rw [vectorDivJet_value]
  simp [closedJet_value_add, valueMapJet_value, matrixUnit_apply, operatorBasis]

theorem partialJet_add_actual {dimension : ℕ} (axis : Fin 2) (first second : ClosedJet dimension) :
    partialJet axis (first + second) = partialJet axis first + partialJet axis second :=
  map_add (partialJetLinear dimension axis) first second

theorem partialJet_sub_actual {dimension : ℕ} (axis : Fin 2) (first second : ClosedJet dimension) :
    partialJet axis (first - second) = partialJet axis first - partialJet axis second :=
  map_sub (partialJetLinear dimension axis) first second

theorem partialJet_neg_actual {dimension : ℕ} (axis : Fin 2) (field : ClosedJet dimension) :
    partialJet axis (-field) = -partialJet axis field := map_neg (partialJetLinear dimension axis) field

/-- The actual two-dimensional Cartesian Hodge identity, with the accepted J. -/
theorem cartesian_hodge (field : ClosedJet 2) :
    planarLaplacian 2 field = gradientJet (vectorDivJet field) +
      valueMapJet quarterValueMap (gradientJet (planarCurlJet field)) := by
  have div := vectorDivJet_explicit field
  have curl : planarCurlJet field = valueMapJet (matrixUnit 0 1) (partialJet 0 field) -
      valueMapJet (matrixUnit 0 0) (partialJet 1 field) := rfl
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  change (partialJet 0 (partialJet 0 field) + partialJet 1 (partialJet 1 field)).value point coordinate = _
  simp only [closedJet_value_add, ContinuousMap.add_apply, valueMapJet_value, gradientJet_value]
  rw [div, curl]
  simp only [partialJet_add_actual, partialJet_neg_actual, partialJet_valueMap,
    partialJets_commute 0 1, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    ContinuousMap.add_apply, ContinuousMap.neg_apply, valueMapJet_value]
  fin_cases coordinate <;>
    simp [quarterValueMap, quarterValueLinear, matrixUnit_apply, operatorBasis] <;> ring

end Grad.CartesianUncompressed
