import AKCG6ActualMatrixWeakLeadingSplit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct
open Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

/-- Actual full coefficient multiplication uses exactly the available
spatial order. Its finite additional reserve is only in the cell coordinate. -/
def startupActualMatrixGraph {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (reserve : order - 1 ≤ weight) (field : GraphGrade input order weight openUnitDisk) :
    GraphGrade output order 0 openUnitDisk := by
  let original := originalMatrixKernel admissible family coherent (base input order openUnitDisk (fun _ => weight) field)
  let derivatives := fun index : JetIndex order =>
    originalMatrixKernel admissible family coherent
      (orderedDerivative input order (degree index) openUnitDisk (fun _ => weight) index.property field (derivativeWord index)) +
    startupMatrixOrderedRemainder admissible family coherent (derivativeWord index) index.property
      (show degree index - 1 ≤ weight from (Nat.sub_le_sub_right index.property 1).trans reserve) field
  have weak (index : JetIndex order) :
      HasWeakOrderedDerivative output openUnitDisk (degree index) (derivativeWord index) original (derivatives index) :=
    startupActualMatrix_weakLeadingSplit admissible family coherent (derivativeWord index) index.property
      ((Nat.sub_le_sub_right index.property 1).trans reserve) field
  have zero : derivatives (zeroIndex order) = original :=
    (Grad.WeakTesting.Commutation.zero output openUnitDisk openUnitDisk_isOpen (derivativeWord (zeroIndex order))
      original (derivatives (zeroIndex order))).mp (weak (zeroIndex order))
  exact startupGraphFromWeak original derivatives zero weak

theorem startupActualMatrixGraph_base {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (reserve : order - 1 ≤ weight) (field : GraphGrade input order weight openUnitDisk) :
    base output order openUnitDisk (fun _ => 0) (startupActualMatrixGraph admissible family coherent reserve field) =
      originalMatrixKernel admissible family coherent (base input order openUnitDisk (fun _ => weight) field) := by
  unfold startupActualMatrixGraph
  apply startupGraphFromWeak_base

end Grad.CartesianStartup
