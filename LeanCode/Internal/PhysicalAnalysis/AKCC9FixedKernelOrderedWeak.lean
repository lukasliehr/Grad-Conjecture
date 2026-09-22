import AKCC8FixedEmptyAllocationKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000

open MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.RepresentedKernel Grad.RepresentedKernel.SpatialProduct Grad.RepresentedKernel.WeakDerivatives
open Grad.WeightedJets Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

def startupFullWordEquiv (rank : ℕ) : DerivativeIndex rank ≃ Word ((∅ : Finset (Fin rank))ᶜ).card where
  toFun target := fun position => target (Fin.cast (startupEmpty_complement_card rank) position)
  invFun target := fun position => target (Fin.cast (startupEmpty_complement_card rank).symm position)
  left_inv target := by
    funext position
    apply congrArg target
    apply Fin.ext
    rfl
  right_inv target := by
    funext position
    apply congrArg target
    apply Fin.ext
    rfl

theorem startupOrderedDerivative_cast {dimension order first second weight : ℕ}
    (same : first = second) (firstBound : first ≤ order) (secondBound : second ≤ order)
    (field : GraphGrade dimension order weight openUnitDisk) (word : DerivativeIndex second) :
    orderedDerivative dimension order first openUnitDisk (fun _ => weight) firstBound field
      (fun position => word (Fin.cast same position)) =
    orderedDerivative dimension order second openUnitDisk (fun _ => weight) secondBound field word := by
  cases same
  rfl

theorem startupEmpty_inputDerivative {dimension order rank weight : ℕ}
    (bound : rank ≤ order) (field : GraphGrade dimension order weight openUnitDisk) (word : DerivativeIndex rank) :
    inputDerivative dimension order rank weight openUnitDisk bound field ∅ (startupFullWordEquiv rank word) =
      orderedDerivative dimension order rank openUnitDisk (fun _ => weight) bound field word := by
  exact startupOrderedDerivative_cast (startupEmpty_complement_card rank) _ bound field word

theorem startupFixed_orderedWeak_allocated {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {input output order rank weight : ℕ}
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output)
    (measurable : Measurable coefficient) (integrable : Integrable coefficient measure)
    (word : DerivativeIndex rank) (bound : rank ≤ order)
    (field : GraphGrade input order weight openUnitDisk) :
    HasWeakOrderedDerivative output openUnitDisk rank word
      (Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant actionMeasurable coefficient measurable integrable)
        (base input order openUnitDisk (fun _ => weight) field))
      (∑ selected : Finset (Fin rank), ∑ target : Word selectedᶜ.card,
        operator (allocatedData (startupFixedRawData measure orthogonal invariant actionMeasurable coefficient measurable integrable)
          word selected target) (0, 0) 0
          (inputDerivative input order rank weight openUnitDisk bound field selected target)) := by
  have consumer := weakGraphConsumer Parameter measure input output order rank weight 1 (by norm_num)
  dsimp only [derivativeCandidate] at consumer
  rw [show Grad.SpatialDilation.disk 1 = openUnitDisk from openUnitDisk_eq_ball.symm] at consumer
  have weak := consumer (startupFixedRawData measure orthogonal invariant actionMeasurable coefficient measurable integrable)
    word bound
    (fun selected target => allocatedData (startupFixedRawData measure orthogonal invariant actionMeasurable coefficient measurable integrable) word selected target)
    (fun selected target => allocatedData_specification (startupFixedRawData measure orthogonal invariant actionMeasurable coefficient measurable integrable) word selected target) field
  rw [startupFixedRawData_operator] at weak
  exact weak

end Grad.CartesianStartup
