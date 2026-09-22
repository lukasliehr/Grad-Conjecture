import ANT3CartesianRadialRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.CartesianScalarElimination
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.NonlinearRange Grad.NonlinearDivision Grad.CircularHighWeak

private theorem eliminate_skew_pair {E : Type*} [AddCommGroup E] [Module ℂ E]
    (rotation : E →ₗ[ℂ] E) (first second source forcing : E)
    (firstEquation : rotation first - (2 : ℂ) • second = rotation source)
    (secondEquation : rotation second + (2 : ℂ) • first = rotation forcing) :
    rotation (rotation first) + (4 : ℂ) • first =
      rotation (rotation source) + (2 : ℂ) • rotation forcing := by
  have derivative := congrArg rotation firstEquation
  rw [map_sub, map_smul] at derivative
  have substitution := eq_sub_of_add_eq secondEquation
  calc
    _ = rotation (rotation first) - (2 : ℂ) •
        (rotation forcing - (2 : ℂ) • first) + (2 : ℂ) • rotation forcing := by module
    _ = rotation (rotation first) - (2 : ℂ) • rotation second + (2 : ℂ) • rotation forcing := by rw [← substitution]
    _ = _ := by rw [derivative]

/-- Genuine first-order scalar equations obtained by applying Cartesian
divergence and curl to the actual homogeneous vector equation. -/
theorem homogeneous_divcurl (theta : ClosedJet 1) (vector : ClosedJet 2)
    (equation : rotationJet vector + valueMapJet quarterValueMap vector = gradientJet (rotationJet theta)) :
    rotationJet (vectorDivJet vector) - (2 : ℂ) • planarCurlJet vector = rotationJet (laplacianJet theta) ∧
      rotationJet (planarCurlJet vector) + (2 : ℂ) • vectorDivJet vector = 0 := by
  have first := congrArg vectorDivJet equation
  rw [vectorDivJet_rotationPlusQuarter, vectorDivJet_gradient, laplacianJet_rotation] at first
  have second := congrArg planarCurlJet equation
  rw [planarCurlJet_rotationPlusQuarter, planarCurlJet_gradient] at second
  exact ⟨first, second⟩

/-- Genuine first-order radial and tangential contractions on the closed disk.
No polar denominator or punctured-domain assumption is used. -/
theorem homogeneous_radial_tangent (theta : ClosedJet 1) (vector : ClosedJet 2)
    (equation : rotationJet vector + valueMapJet quarterValueMap vector = gradientJet (rotationJet theta)) :
    rotationJet (vectorRadialJet vector) - (2 : ℂ) • vectorTangentJet vector = rotationJet (eulerJet theta) ∧
      rotationJet (vectorTangentJet vector) + (2 : ℂ) • vectorRadialJet vector = rotationJet (rotationJet theta) := by
  have first := congrArg vectorRadialJet equation
  rw [vectorRadialJet_rotationPlusQuarter, vectorRadialJet_gradient, eulerJet_rotation] at first
  have second := congrArg vectorTangentJet equation
  rw [vectorTangentJet_rotationPlusQuarter, vectorTangentJet_gradient] at second
  exact ⟨first, second⟩

theorem homogeneous_div_polynomial (theta : ClosedJet 1) (vector : ClosedJet 2)
    (equation : rotationJet vector + valueMapJet quarterValueMap vector = gradientJet (rotationJet theta)) :
    rotationJet (rotationJet (vectorDivJet vector)) + (4 : ℂ) • vectorDivJet vector =
      rotationJet (rotationJet (laplacianJet theta)) := by
  have laws := homogeneous_divcurl theta vector equation
  have second : rotationJetLinear (planarCurlJet vector) + (2 : ℂ) • vectorDivJet vector = rotationJetLinear 0 :=
    laws.2.trans (map_zero rotationJetLinear).symm
  have result := eliminate_skew_pair rotationJetLinear (vectorDivJet vector) (planarCurlJet vector)
    (laplacianJet theta) 0 laws.1 second
  simpa only [map_zero, smul_zero, add_zero, rotationJetLinear_apply] using result

theorem homogeneous_radial_polynomial (theta : ClosedJet 1) (vector : ClosedJet 2)
    (equation : rotationJet vector + valueMapJet quarterValueMap vector = gradientJet (rotationJet theta)) :
    rotationJet (rotationJet (vectorRadialJet vector)) + (4 : ℂ) • vectorRadialJet vector =
      rotationJet (rotationJet (eulerJet theta + (2 : ℂ) • theta)) := by
  have laws := homogeneous_radial_tangent theta vector equation
  have result := eliminate_skew_pair rotationJetLinear (vectorRadialJet vector) (vectorTangentJet vector)
    (eulerJet theta) (rotationJet theta) laws.1 laws.2
  change rotationJetLinear (rotationJetLinear (vectorRadialJet vector)) + (4 : ℂ) • vectorRadialJet vector =
    rotationJetLinear (rotationJetLinear (eulerJet theta + (2 : ℂ) • theta))
  rw [map_add, map_smul, map_add, map_smul]
  exact result

end Grad.CartesianScalarElimination
