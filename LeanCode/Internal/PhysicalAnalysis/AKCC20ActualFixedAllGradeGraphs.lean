import AKCC19SameFixedWeightedGraph
import AKBW9CovectorCoefficientContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Radial
open Grad.WeightedJets

def StartupPreservesGraph {input output : ℕ} (kernel : StartupL2 input →L[ℂ] StartupL2 output) : Prop :=
  ∀ (order weight : ℕ) (field : GraphGrade input order weight openUnitDisk),
    ∃ image : GraphGrade output order weight openUnitDisk,
      base output order openUnitDisk (fun _ => weight) image =
        kernel (base input order openUnitDisk (fun _ => weight) field)

theorem startupPoint_preservesGraph {input output : ℕ} (mapping : OperatorValue input output)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) : StartupPreservesGraph (startupPointKernel mapping orthogonal) := by
  intro order weight field
  let invariant := fun (_ : ℝ) (point : Spatial) => show (‖orthogonal point‖ < 1 ↔ ‖point‖ < 1) by rw [orthogonal.norm_map]
  have actionMeasurable : Measurable (fun pair : ℝ × Spatial => orthogonal pair.2) :=
    (orthogonal.continuous.comp continuous_snd).measurable
  have liftedMeasurable (rank : ℕ) : Measurable (fun (_ : ℝ) => startupCovectorCoefficient rank orthogonal mapping) := measurable_const
  let liftedIntegrable := fun rank : ℕ => integrable_const (μ := Measure.dirac (0 : ℝ)) (startupCovectorCoefficient rank orthogonal mapping)
  refine ⟨startupFixedWeightedGraph (Measure.dirac (0 : ℝ)) (fun _ => orthogonal) invariant actionMeasurable
    (fun _ => mapping) measurable_const (integrable_const mapping) liftedMeasurable liftedIntegrable field, ?_⟩
  exact startupFixedWeightedGraph_base (Measure.dirac (0 : ℝ)) (fun _ => orthogonal) invariant actionMeasurable
    (fun _ => mapping) measurable_const (integrable_const mapping) liftedMeasurable liftedIntegrable field

theorem startupAngular_preservesGraph (dimension : ℕ) (scalar : ℝ → ℂ) (smooth : ContDiff ℝ ∞ scalar) :
    StartupPreservesGraph (startupAngularKernel dimension scalar smooth) := by
  intro order weight field
  let invariant := fun angle (point : Spatial) => show (‖planeRotationEquiv angle point‖ < 1 ↔ ‖point‖ < 1) by
    rw [(planeRotationEquiv angle).norm_map]
  let coefficient := startupAngularCoefficient dimension scalar
  have continuousCoefficient : Continuous coefficient := startupAngularCoefficient_continuous dimension scalar smooth
  have integrable : Integrable coefficient (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))) :=
    continuousCoefficient.integrableOn_Icc
  have liftedMeasurable (rank : ℕ) : Measurable (fun angle => startupCovectorCoefficient rank (planeRotationEquiv angle) (coefficient angle)) :=
    (startupCovectorCoefficient_continuous rank planeRotationEquiv continuous_planeRotation_joint coefficient continuousCoefficient).measurable
  have liftedIntegrable (rank : ℕ) : Integrable (fun angle => startupCovectorCoefficient rank (planeRotationEquiv angle) (coefficient angle))
      (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))) :=
    startupCovectorCoefficient_integrable _ rank planeRotationEquiv coefficient integrable (liftedMeasurable rank).aestronglyMeasurable
  refine ⟨startupFixedWeightedGraph (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))) planeRotationEquiv invariant
    continuous_planeRotation_joint.measurable coefficient continuousCoefficient.measurable integrable liftedMeasurable liftedIntegrable field, ?_⟩
  exact startupFixedWeightedGraph_base (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))) planeRotationEquiv invariant
    continuous_planeRotation_joint.measurable coefficient continuousCoefficient.measurable integrable liftedMeasurable liftedIntegrable field

end Grad.CartesianStartup
