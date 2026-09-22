import ANG28ActualAN20

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Grad.CircularHighWeak
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- Immediate original-source consumer: F is the literal smooth disk jet,
the source on the right is its literal iterated R, and the norm is the
ordinary sum of Cartesian derivatives through precisely order=a−1. -/
theorem originalSourceAN20_consumer (parameter : ℝ) (order : ℕ) (source : ClosedJet 1)
    (high : closedL2Core source ∈ highDiskL2) :
    ∃ derivative : highDiskGrade,
      HasH1AngularPower (order + 1) (highRobinWeakInverse parameter ⟨closedL2Core source, high⟩) derivative ∧
      (∀ test : highDiskGrade, robinValue parameter derivative test =
        -inner ℂ (highRotation test) (closedL2Core (rotationJetPower order source))) ∧
      ‖derivative‖ ≤ (2 * unitRotationPowerConstant order) * ‖unitSobolevRow order source‖ := by
  let completed := unitDiskCoreInto order source
  have coreHigh : sourceBulk order completed.val ∈ highDiskL2 :=
    (congrArg (fun value : DiskL2 1 => value ∈ highDiskL2) (unitDiskBulk_core order source).symm).mp high
  have sources : sourceHighBulk order completed.val = (⟨closedL2Core source, high⟩ : highDiskL2) := by
    apply Subtype.ext
    exact (highL2Projection_fixed ⟨sourceBulk order completed.val, coreHigh⟩).trans (unitDiskBulk_core order source)
  have transfer := congrArg (fun value : highDiskL2 =>
    HasH1AngularPower (order + 1) (highRobinWeakInverse parameter value)
      (angularWeakSolutionPower parameter order completed.val)) sources
  have original : sourceRotationPower order completed.val = closedL2Core (rotationJetPower order source) :=
    (sourceRotationPower_core order (Finsupp.single 0 source)).trans
      (congrArg (fun value : ClosedJet 1 => closedL2Core (rotationJetPower order value)) Finsupp.single_eq_same)
  refine ⟨angularWeakSolutionPower parameter order completed.val,
    transfer.mp (actualAngularRegularity parameter order completed.val).1, ?_,
    (angularWeakSolutionPower_bound parameter order completed.val).trans_eq ?_⟩
  · intro test
    exact (angularWeakSolutionPower_original_functional parameter order completed.val coreHigh test).trans
      (congrArg (fun value : DiskL2 1 => -inner ℂ (highRotation test) value) original)
  · exact congrArg (fun value : ℝ => (2 * unitRotationPowerConstant order) * value) (unitDiskCore_norm order source)

end Grad.CircularHighWeak
