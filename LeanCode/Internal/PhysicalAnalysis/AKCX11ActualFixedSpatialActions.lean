import AKCX10ActualMatrixSpatialAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.WeightedJets Grad.WeightedJets.Ordered
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Radial
namespace StartupSpatialAction
variable {L ell : ℝ}

def identity (rank dimension : ℕ) : StartupSpatialAction rank dimension dimension L ell where
  signed := StartupSignedAction.identity dimension
  ranked := StartupRankOperator.identity rank dimension
  preserves order family regular := by
    intro power weight
    obtain ⟨graph,same⟩ := regular power weight
    exact ⟨graph,same⟩
  leading family _ field fieldSame image imageSame := by
    have same : base dimension rank openUnitDisk (fun _ => 0) image =
        base dimension rank openUnitDisk (fun _ => 0) field := imageSame.trans fieldSame.symm
    have derivativeSame := startupOrderedDerivative_sameBase image le_rfl field le_rfl same
    exact ⟨0,by rw [derivativeSame,map_zero,add_zero]; rfl⟩

def point {input output : ℕ} (rank : ℕ) (mapping : OperatorValue input output)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) : StartupSpatialAction rank input output L ell where
  signed := StartupSignedAction.fixed (startupPointKernel mapping orthogonal) (startupPointFirstGraph mapping orthogonal)
    (startupPointFirstGraph_compatible mapping orthogonal) (startupPointKernel_cellwise mapping orthogonal)
  ranked := StartupRankOperator.point rank mapping orthogonal
  preserves _ _ regular := regular.map _ (startupPointKernel_cellwise mapping orthogonal) (startupPoint_preservesGraph mapping orthogonal)
  leading family _ field fieldSame image imageSame := by
    refine ⟨0,?_⟩
    rw [map_zero,add_zero]
    have same : base output rank openUnitDisk (fun _ => 0) image =
        startupPointKernel mapping orthogonal (base input rank openUnitDisk (fun _ => 0) field) := by
      rw [fieldSame]
      exact imageSame
    exact startupActualFixed_rankDerivative (Measure.dirac (0 : ℝ)) (fun _ => orthogonal)
      (fun _ point => by change (‖orthogonal point‖ < 1 ↔ ‖point‖ < 1); rw [orthogonal.norm_map])
      (orthogonal.continuous.comp continuous_snd).measurable (fun _ => mapping)
      measurable_const (integrable_const mapping) measurable_const field le_rfl image le_rfl same

def angular (dimension rank : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) :
    StartupSpatialAction rank dimension dimension L ell where
  signed := StartupSignedAction.fixed (startupAngularKernel dimension weight smooth) (startupAngularFirstGraph dimension weight smooth)
    (startupAngularFirstGraph_compatible dimension weight smooth) (startupAngularKernel_cellwise dimension weight smooth)
  ranked := StartupRankOperator.angular dimension rank weight smooth
  preserves _ _ regular := regular.map _ (startupAngularKernel_cellwise dimension weight smooth) (startupAngular_preservesGraph dimension weight smooth)
  leading family _ field fieldSame image imageSame := by
    refine ⟨0,?_⟩
    rw [map_zero,add_zero]
    have same : base dimension rank openUnitDisk (fun _ => 0) image =
        startupAngularKernel dimension weight smooth (base dimension rank openUnitDisk (fun _ => 0) field) := by
      rw [fieldSame]
      exact imageSame
    exact startupActualFixed_rankDerivative (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))) planeRotationEquiv
      (fun angle point => by change (‖planeRotationEquiv angle point‖ < 1 ↔ ‖point‖ < 1); rw [(planeRotationEquiv angle).norm_map])
      continuous_planeRotation_joint.measurable (startupAngularCoefficient dimension weight)
      (startupAngularCoefficient_continuous dimension weight smooth).measurable
      (startupAngularCoefficient_continuous dimension weight smooth).integrableOn_Icc
      (startupCovectorCoefficient_continuous rank planeRotationEquiv continuous_planeRotation_joint
        (startupAngularCoefficient dimension weight) (startupAngularCoefficient_continuous dimension weight smooth)).measurable
      field le_rfl image le_rfl same

end StartupSpatialAction
end Grad.CartesianStartup
