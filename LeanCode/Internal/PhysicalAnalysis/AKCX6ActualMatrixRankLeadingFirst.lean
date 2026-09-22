import AKCX5SameSignedAllWeightSpatialGraphs
import AKBW13FullMatrixRankLift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct
open Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

/-- The actual matrix's ordered derivative equals the unchanged accepted
rank operator on the top derivative, plus a genuine first graph in the
same flattened tensor carrier. Only lower spatial allocations pay for the
remainder. The image graph is any representative of the actual output. -/
theorem startupActualMatrix_rankLeadingFirst {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order rank weight imageOrder imageWeight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (bound : rank ≤ order) (reserve : rank ≤ weight)
    (field : GraphGrade input order weight openUnitDisk)
    (image : GraphGrade output imageOrder imageWeight openUnitDisk) (imageBound : rank ≤ imageOrder)
    (sameImage : base output imageOrder openUnitDisk (fun _ => imageWeight) image =
      originalMatrixKernel admissible family coherent (base input order openUnitDisk (fun _ => weight) field)) :
    ∃ remainder : StartupFirst (startupTensorDimension output rank),
      startupTensorFieldEquiv output rank
        (orderedDerivative output imageOrder rank openUnitDisk (fun _ => imageWeight) imageBound image) =
      (StartupRankOperator.matrix admissible rank family coherent).coarse
        (startupTensorFieldEquiv input rank
          (orderedDerivative input order rank openUnitDisk (fun _ => weight) bound field)) +
      base (startupTensorDimension output rank) 1 openUnitDisk (fun _ => 0) remainder := by
  let firsts (word : Grad.TensorBootstrap.DerivativeIndex rank) : StartupFirst output :=
    (startupMatrixOrderedRemainder_first admissible family coherent word bound reserve field).choose
  have firstSame (word : Grad.TensorBootstrap.DerivativeIndex rank) :
      base output 1 openUnitDisk (fun _ => 0) (firsts word) =
      startupMatrixOrderedRemainder admissible family coherent word bound (by omega) field :=
    (startupMatrixOrderedRemainder_first admissible family coherent word bound reserve field).choose_spec
  let remTensor : Tensor rank (StartupL2 output) := WithLp.toLp 2 (fun word =>
    startupMatrixOrderedRemainder admissible family coherent word bound (show rank-1 ≤ weight from by omega) field)
  let leading := hilbertLift (Index := Grad.TensorBootstrap.DerivativeIndex rank)
    (originalMatrixKernel admissible family coherent)
    (orderedDerivative input order rank openUnitDisk (fun _ => weight) bound field)
  have derivativeSame :
      orderedDerivative output imageOrder rank openUnitDisk (fun _ => imageWeight) imageBound image = leading+remTensor := by
    apply startupOrderedDerivative_unique image imageBound
    intro word
    rw [sameImage]
    exact startupActualMatrix_weakLeadingSplit admissible family coherent word bound (by omega) field
  refine ⟨startupTensorFirstEquiv output rank (WithLp.toLp 2 firsts),?_⟩
  rw [derivativeSame,map_add]
  have flatFirst : base (startupTensorDimension output rank) 1 openUnitDisk (fun _ => 0)
      (startupTensorFirstEquiv output rank (WithLp.toLp 2 firsts)) =
      startupTensorFieldEquiv output rank (startupTensorFirstValues (WithLp.toLp 2 firsts)) :=
    startupTensorFirstEquiv_base output rank (WithLp.toLp 2 firsts)
  rw [flatFirst]
  change startupTensorFieldEquiv output rank leading + startupTensorFieldEquiv output rank remTensor = _
  have remSame : startupTensorFirstValues (WithLp.toLp 2 firsts) = remTensor := by
    apply PiLp.ext
    intro word
    exact firstSame word
  rw [remSame]
  congr 1
  exact (StartupRankOperator.entrywise_coarse rank (originalMatrixKernel admissible family coherent)
    (startupMatrixFirstGraphCLM admissible family coherent)
    (startupMatrixFirstGraph_compatible admissible family coherent) _).symm

end Grad.CartesianStartup
