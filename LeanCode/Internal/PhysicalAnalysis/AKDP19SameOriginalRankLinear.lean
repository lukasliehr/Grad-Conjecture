import AKDP18ActualCurrentCoefficientProfiles
import AKDR4SameOriginalFieldAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.ActualOriginalSourceMoments Grad.ActualOriginalSourceFirst Grad.TensorBootstrap
open Grad.WeightedJets.Ordered Grad.OriginalCoreRealization
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Radial

/-- The literal full ordered original derivative tensor is linear. -/
def startupOriginalRankLinear {dimension : ℕ} (parameters : PhaseParameters) (rank : ℕ) :
    ACore parameters dimension →ₗ[ℂ] StartupL2 (startupTensorDimension dimension rank) where
  toFun := startupOriginalRankField parameters rank
  map_add' first second := by
    let one := originalSourceSpatialGraph parameters first rank
    let two := originalSourceSpatialGraph parameters second rank
    have same : base dimension rank openUnitDisk (fun _ => 0) (one+two) =
        (originalSourceMoments parameters (first+second)).field := by
      rw [map_add,originalSourceSpatialGraph_base,originalSourceSpatialGraph_base]
      exact (map_add (originalSourceFieldLinear parameters) first second).symm
    rw [← startupOriginalRankField_graph parameters (first+second) (one+two) same le_rfl,map_add,map_add,
      startupOriginalRankField_graph parameters first one (originalSourceSpatialGraph_base parameters first rank),
      startupOriginalRankField_graph parameters second two (originalSourceSpatialGraph_base parameters second rank)]
  map_smul' scalar field := by
    let one := originalSourceSpatialGraph parameters field rank
    have same : base dimension rank openUnitDisk (fun _ => 0) (scalar • one) =
        (originalSourceMoments parameters (scalar • field)).field := by
      rw [map_smul,originalSourceSpatialGraph_base]
      exact (map_smul (originalSourceFieldLinear parameters) scalar field).symm
    simp only [RingHom.id_apply]
    rw [← startupOriginalRankField_graph parameters (scalar • field) (scalar • one) same le_rfl,map_smul,map_smul,
      startupOriginalRankField_graph parameters field one (originalSourceSpatialGraph_base parameters field rank)]

/-- A genuine angular kernel has zero original spatial rank remainder. -/
theorem startupOriginalAngular_rank_exact {dimension : ℕ} (parameters : PhaseParameters)
    (rank : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (core image : ACore parameters dimension)
    (same : (originalSourceMoments parameters image).field =
      startupAngularKernel dimension weight smooth (originalSourceMoments parameters core).field) :
    startupOriginalRankField parameters rank image =
      (StartupRankOperator.angular dimension rank weight smooth).coarse (startupOriginalRankField parameters rank core) := by
  let source := originalSourceSpatialGraph parameters core rank
  let target := originalSourceSpatialGraph parameters image rank
  have identified : base dimension rank openUnitDisk (fun _ => 0) target =
      startupAngularKernel dimension weight smooth (base dimension rank openUnitDisk (fun _ => 0) source) := by
    rw [originalSourceSpatialGraph_base,originalSourceSpatialGraph_base]
    exact same
  have actual := startupActualFixed_rankDerivative (volume.restrict (Set.Icc (0 : ℝ) (2*Real.pi))) planeRotationEquiv
    (fun angle point => by change ‖planeRotationEquiv angle point‖ < 1 ↔ ‖point‖ < 1; rw [(planeRotationEquiv angle).norm_map])
    continuous_planeRotation_joint.measurable (startupAngularCoefficient dimension weight)
    (startupAngularCoefficient_continuous dimension weight smooth).measurable
    (startupAngularCoefficient_continuous dimension weight smooth).integrableOn_Icc
    (startupCovectorCoefficient_continuous rank planeRotationEquiv continuous_planeRotation_joint
      (startupAngularCoefficient dimension weight) (startupAngularCoefficient_continuous dimension weight smooth)).measurable
    source le_rfl target le_rfl identified
  rw [startupOriginalRankField_graph parameters image target (originalSourceSpatialGraph_base parameters image rank),
    startupOriginalRankField_graph parameters core source (originalSourceSpatialGraph_base parameters core rank)] at actual
  exact actual

/-- The actual reflected covectors are retained in every point action. -/
theorem startupOriginalPoint_rank_exact {input output : ℕ} (parameters : PhaseParameters)
    (rank : ℕ) (mapping : Grad.GaugeCoefficients.Algebra.OperatorValue input output)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (core : ACore parameters input) (image : ACore parameters output)
    (same : (originalSourceMoments parameters image).field =
      startupPointKernel mapping orthogonal (originalSourceMoments parameters core).field) :
    startupOriginalRankField parameters rank image =
      (StartupRankOperator.point rank mapping orthogonal).coarse (startupOriginalRankField parameters rank core) := by
  let source := originalSourceSpatialGraph parameters core rank
  let target := originalSourceSpatialGraph parameters image rank
  have identified : base output rank openUnitDisk (fun _ => 0) target =
      startupPointKernel mapping orthogonal (base input rank openUnitDisk (fun _ => 0) source) := by
    rw [originalSourceSpatialGraph_base,originalSourceSpatialGraph_base]
    exact same
  have actual := startupActualFixed_rankDerivative (Measure.dirac (0 : ℝ)) (fun _ => orthogonal)
    (fun _ point => by change ‖orthogonal point‖ < 1 ↔ ‖point‖ < 1; rw [orthogonal.norm_map])
    (orthogonal.continuous.comp continuous_snd).measurable (fun _ => mapping)
    measurable_const (integrable_const mapping) measurable_const source le_rfl target le_rfl identified
  rw [startupOriginalRankField_graph parameters image target (originalSourceSpatialGraph_base parameters image rank),
    startupOriginalRankField_graph parameters core source (originalSourceSpatialGraph_base parameters core rank)] at actual
  exact actual

end Grad.CartesianStartup
