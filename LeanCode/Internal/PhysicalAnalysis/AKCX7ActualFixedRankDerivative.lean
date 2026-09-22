import AKCX6ActualMatrixRankLeadingFirst

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

/-- The literal fixed angular/reflection operator differentiates to its
accepted true covector rank operator in the flattened carrier. This is an
exact identity and introduces no spatial remainder. -/
theorem startupActualFixed_rankDerivative {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {input output order rank weight imageOrder imageWeight : ℕ}
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output)
    (measurable : Measurable coefficient) (integrable : Integrable coefficient measure)
    (liftMeasurable : Measurable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)))
    (field : GraphGrade input order weight openUnitDisk) (bound : rank ≤ order)
    (image : GraphGrade output imageOrder imageWeight openUnitDisk) (imageBound : rank ≤ imageOrder)
    (sameImage : base output imageOrder openUnitDisk (fun _ => imageWeight) image =
      Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant actionMeasurable coefficient measurable integrable)
        (base input order openUnitDisk (fun _ => weight) field)) :
    startupTensorFieldEquiv output rank
      (orderedDerivative output imageOrder rank openUnitDisk (fun _ => imageWeight) imageBound image) =
    (StartupRankOperator.fixed measure rank orthogonal invariant actionMeasurable coefficient integrable liftMeasurable).coarse
      (startupTensorFieldEquiv input rank
        (orderedDerivative input order rank openUnitDisk (fun _ => weight) bound field)) := by
  let liftIntegrable := startupCovectorCoefficient_integrable measure rank orthogonal coefficient integrable
    liftMeasurable.aestronglyMeasurable
  have same : orderedDerivative output imageOrder rank openUnitDisk (fun _ => imageWeight) imageBound image =
      startupFixedTensorKernel measure rank orthogonal invariant actionMeasurable coefficient liftMeasurable liftIntegrable
        (orderedDerivative input order rank openUnitDisk (fun _ => weight) bound field) := by
    apply startupOrderedDerivative_unique image imageBound
    intro word
    rw [sameImage]
    exact startupFixedTensor_orderedWeak measure orthogonal invariant actionMeasurable coefficient measurable integrable
      liftMeasurable liftIntegrable word bound field
  rw [same]
  change startupTensorFieldEquiv output rank ((startupTensorFieldEquiv output rank).symm
    ((StartupRankOperator.fixed measure rank orthogonal invariant actionMeasurable coefficient integrable liftMeasurable).coarse
      (startupTensorFieldEquiv input rank
        (orderedDerivative input order rank openUnitDisk (fun _ => weight) bound field)))) = _
  exact LinearIsometryEquiv.apply_symm_apply _ _

end Grad.CartesianStartup
