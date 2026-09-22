import GC18JetBridge

noncomputable section

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.RepresentedKernel.SpatialProduct
open Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearQuotientBounds Grad.PhysicalFamily
open Grad.NonlinearDivision
open Grad.NonlinearQuotient (radialIntegral diskLaplacian radialIntegral_laplacian)

/-- AO9 before imposing the zero axis numerator: the exact radial primitive
recovers the radial field minus its axis value, including the boundary. -/
theorem radialJet_identity_sub_origin {dimension : ℕ} (field : ClosedJet dimension)
    (radial : IsRotationInvariant field) (point : ClosedDisk) :
    field.value point - field.value closedOrigin =
      ‖point.val‖ ^ 2 • integralCoefficient (laplacianJet field) point := by
  have leftContinuous : Continuous (fun source : SpatialPlane =>
      smoothClosedExtension field source - smoothClosedExtension field 0) :=
    (smoothClosedExtension_smooth field).continuous.sub continuous_const
  have rightContinuous : Continuous (fun source : SpatialPlane =>
      ‖source‖ ^ 2 • radialIntervalValue 0 1 (laplacianJet field) source) :=
    (continuous_norm.pow 2).smul (radialIntervalValue_smooth 0 1 (laplacianJet field)).continuous
  have openAgreement : EqOn (fun source : SpatialPlane =>
      smoothClosedExtension field source - smoothClosedExtension field 0)
      (fun source : SpatialPlane => ‖source‖ ^ 2 • radialIntervalValue 0 1 (laplacianJet field) source)
      (Metric.ball (0 : SpatialPlane) 1) := by
    intro source sourceIn
    change smoothClosedExtension field source - smoothClosedExtension field 0 =
      ‖source‖ ^ 2 • radialIntervalValue 0 1 (laplacianJet field) source
    rw [radialIntegral_laplacian (smoothClosedExtension field) 1
      (smoothClosedExtension_smooth field).contDiffOn
      (fun angle current currentIn => extension_rotation radial angle current currentIn) source sourceIn]
    congr 1
    have closed : source ∈ closedUnitDisk := (mem_ball_zero_iff.mp sourceIn).le
    exact (integralCoefficient_laplacianJet field ⟨source, closed⟩).symm.trans
      (integralCoefficient_eq_intervalValue (laplacianJet field) ⟨source, closed⟩)
  have closedAgreement := openAgreement.closure leftContinuous rightContinuous
  rw [closure_ball (0 : SpatialPlane) one_ne_zero] at closedAgreement
  have equality := closedAgreement (mem_closedBall_zero_iff.mpr point.property)
  change smoothClosedExtension field point.val - smoothClosedExtension field closedOrigin.val =
    ‖point.val‖ ^ 2 • radialIntervalValue 0 1 (laplacianJet field) point.val at equality
  rw [smoothClosedExtension_value, smoothClosedExtension_value,
    ← integralCoefficient_eq_intervalValue] at equality
  exact equality

end Grad.GaugeCoefficients.Physical.RadialLedger
