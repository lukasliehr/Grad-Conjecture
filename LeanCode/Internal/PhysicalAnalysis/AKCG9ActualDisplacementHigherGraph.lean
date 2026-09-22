import AKCG8ActualFixedMatrixDerivativeSplit
import AKCB12FullDisplacementMatrixWeak

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct
open Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

/-- The exact pre-differentiated coefficient and axial-displacement
remainder is in the graph of the available input spatial order. Its
frequency reserve is restored before the full matrix acts. -/
def startupDisplacementMatrixGraph {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (baseline : CartesianMultiIndex) (power : ℕ)
    (reserve : cartesianOrder baseline + order - 1 ≤ weight)
    (field : GraphGrade input order weight openUnitDisk) : GraphGrade output order 0 openUnitDisk := by
  let original := startupDisplacementKernel admissible family coherent (startupShiftedIndex baseline (0,0)) power
    (startupReservedDerivative admissible (startupShiftedZero_reserve baseline reserve) (zeroIndex order) field)
  let derivatives := fun index : JetIndex order =>
    ∑ selected : Finset (Fin (degree index)),
      startupDisplacementKernel admissible family coherent
        (startupShiftedIndex baseline (selectedIndex (derivativeWord index) selected)) power
        (startupReservedDerivative admissible (startupShiftedSelected_reserve baseline (derivativeWord index) selected
          (show cartesianOrder baseline + degree index - 1 ≤ weight from by have degreeBound : degree index ≤ order := index.property; omega))
          (startupComplementIndex (derivativeWord index) index.property selected) field)
  have weak (index : JetIndex order) :
      HasWeakOrderedDerivative output openUnitDisk (degree index) (derivativeWord index) original (derivatives index) :=
    startupDisplacementMatrix_baselineWeak admissible family coherent baseline power (derivativeWord index) index.property
      (by have degreeBound : degree index ≤ order := index.property; omega) field
  have zero : derivatives (zeroIndex order) = original :=
    (Grad.WeakTesting.Commutation.zero output openUnitDisk openUnitDisk_isOpen (derivativeWord (zeroIndex order))
      original (derivatives (zeroIndex order))).mp (weak (zeroIndex order))
  exact startupGraphFromWeak original derivatives zero weak

theorem startupDisplacementMatrixGraph_base {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (baseline : CartesianMultiIndex) (power : ℕ)
    (reserve : cartesianOrder baseline + order - 1 ≤ weight)
    (field : GraphGrade input order weight openUnitDisk) :
    base output order openUnitDisk (fun _ => 0)
      (startupDisplacementMatrixGraph admissible family coherent baseline power reserve field) =
      startupDisplacementKernel admissible family coherent (startupShiftedIndex baseline (0,0)) power
        (startupReservedDerivative admissible (startupShiftedZero_reserve baseline reserve) (zeroIndex order) field) := by
  unfold startupDisplacementMatrixGraph
  apply startupGraphFromWeak_base

def startupCellDisplacementGraph {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (power : ℕ) (reserve : order - 1 ≤ weight)
    (field : GraphGrade input order weight openUnitDisk) : GraphGrade output order 0 openUnitDisk :=
  startupDisplacementMatrixGraph admissible family coherent (0,0) power
    (by simpa only [cartesianOrder, zero_add] using reserve) field

theorem startupCellDisplacementGraph_base {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (power : ℕ) (reserve : order - 1 ≤ weight)
    (field : GraphGrade input order weight openUnitDisk) :
    base output order openUnitDisk (fun _ => 0)
      (startupCellDisplacementGraph admissible family coherent power reserve field) =
      startupDisplacementKernel admissible family coherent zeroDerivativeIndex power
        (base input order openUnitDisk (fun _ => weight) field) := by
  unfold startupCellDisplacementGraph
  rw [startupDisplacementMatrixGraph_base]
  change startupDisplacementKernel admissible family coherent zeroDerivativeIndex power
    (startupReservedDerivative admissible (Nat.zero_le weight) (zeroIndex order) field) = _
  rw [startupReservedDerivative_zero, Realization.recoveredDerivative_zero]

end Grad.CartesianStartup
