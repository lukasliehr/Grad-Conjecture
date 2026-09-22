import AKCG7ActualMatrixAllOrderGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct
open Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

/-- Differentiate the actual fixed angular/reflection operator after full
coefficient multiplication. All coefficient derivatives remain in the
explicit nonempty-allocation remainder, with their original input reserve. -/
theorem startupActualFixedMatrix_weakLeadingSplit
    {Parameter : Type*} [MeasurableSpace Parameter] (measure : Measure Parameter) [SigmaFinite measure]
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input middle output order rank weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input middle) (coherent : FamilyCoherent family)
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue middle output)
    (measurable : Measurable coefficient) (integrable : Integrable coefficient measure)
    (liftMeasurable : Measurable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)))
    (liftIntegrable : Integrable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)) measure)
    (word : DerivativeIndex rank) (bound : rank ≤ order) (reserve : order - 1 ≤ weight)
    (field : GraphGrade input order weight openUnitDisk) :
    let derivatives := orderedDerivative input order rank openUnitDisk (fun _ => weight) bound field
    let leading := hilbertLift (Index := DerivativeIndex rank) (originalMatrixKernel admissible family coherent) derivatives
    let remainder := WithLp.toLp 2 (fun target : DerivativeIndex rank =>
      startupMatrixOrderedRemainder admissible family coherent target bound
        ((Nat.sub_le_sub_right bound 1).trans reserve) field)
    HasWeakOrderedDerivative output openUnitDisk rank word
      (Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant actionMeasurable coefficient measurable integrable)
        (originalMatrixKernel admissible family coherent (base input order openUnitDisk (fun _ => weight) field)))
      ((startupFixedTensorKernel measure rank orthogonal invariant actionMeasurable coefficient liftMeasurable liftIntegrable leading +
        startupFixedTensorKernel measure rank orthogonal invariant actionMeasurable coefficient liftMeasurable liftIntegrable remainder) word) := by
  dsimp only
  let image := startupActualMatrixGraph admissible family coherent reserve field
  have weak (target : DerivativeIndex rank) :
      HasWeakOrderedDerivative middle openUnitDisk rank target
        (base middle order openUnitDisk (fun _ => 0) image)
        ((hilbertLift (Index := DerivativeIndex rank) (originalMatrixKernel admissible family coherent)
          (orderedDerivative input order rank openUnitDisk (fun _ => weight) bound field) +
          WithLp.toLp 2 (fun other : DerivativeIndex rank =>
            startupMatrixOrderedRemainder admissible family coherent other bound
              ((Nat.sub_le_sub_right bound 1).trans reserve) field)) target) := by
    rw [startupActualMatrixGraph_base]
    exact startupActualMatrix_weakLeadingSplit admissible family coherent target bound
      ((Nat.sub_le_sub_right bound 1).trans reserve) field
  have actual := startupFixedTensor_exactSplit measure orthogonal invariant actionMeasurable coefficient measurable integrable
    liftMeasurable liftIntegrable image bound _ _ weak word
  rw [startupActualMatrixGraph_base] at actual
  exact actual

end Grad.CartesianStartup
