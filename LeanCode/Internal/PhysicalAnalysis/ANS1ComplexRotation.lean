import ANJ13ExactHighRobinConsumer

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualAngularInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.GaugeCoefficients.Radial Grad.PhysicalFamily Grad.ActualSmoothPDE

/-- Compact Cartesian rotation integral: there is no singular division at the axis. -/
def kernelRotationValue {dimension : ℕ} (weight : ℝ → ℂ) (field : SpatialPlane → ComplexEuclidean dimension)
    (point : SpatialPlane) : ComplexEuclidean dimension :=
  (2 * Real.pi)⁻¹ • ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
    weight angle • field (planeRotationAction angle point)

theorem kernelRotationValue_smooth {dimension : ℕ} (weight : ℝ → ℂ) (weightSmooth : ContDiff ℝ ∞ weight)
    (field : SpatialPlane → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (kernelRotationValue weight field) := by
  have integrand : ContDiff ℝ ∞ (fun argument : SpatialPlane × ℝ =>
      weight argument.2 • field (planeRotationAction argument.2 argument.1)) :=
    (weightSmooth.comp contDiff_snd).smul
      (smooth.comp cartesianRotation_smooth)
  apply contDiffOn_univ.mp
  change ContDiffOn ℝ ∞ (fun point => (2 * Real.pi)⁻¹ • ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
    weight angle • field (planeRotationAction angle point)) univ
  exact (contDiffOn_const (c := ((2 * Real.pi)⁻¹ : ℝ))).smul
    (contDiffOn_compactIntegral isOpen_univ integrand.contDiffOn 0 (2 * Real.pi))

def kernelRotationJet {dimension : ℕ} (weight : ℝ → ℂ) (weightSmooth : ContDiff ℝ ∞ weight)
    (field : ClosedJet dimension) : ClosedJet dimension :=
  globalClosedJet (kernelRotationValue weight (smoothClosedExtension field))
    (kernelRotationValue_smooth weight weightSmooth _ (smoothClosedExtension_smooth field))

theorem kernelRotationJet_value {dimension : ℕ} (weight : ℝ → ℂ) (weightSmooth : ContDiff ℝ ∞ weight)
    (field : ClosedJet dimension) (point : ClosedDisk) :
    (kernelRotationJet weight weightSmooth field).value point =
      (2 * Real.pi)⁻¹ • ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
        weight angle • field.value (rotatedPoint angle point) := by
  change kernelRotationValue weight (smoothClosedExtension field) point.val = _
  unfold kernelRotationValue
  congr 1
  apply integral_congr_ae
  filter_upwards with angle
  have literal := smoothClosedExtension_value field (rotatedPoint angle point)
  simpa only [physicalRotation_eq_orthogonal, planeRotationEquiv_apply, rotatedPoint] using
    congrArg (fun value : ComplexEuclidean dimension => weight angle • value) literal


end Grad.ActualAngularInverse
