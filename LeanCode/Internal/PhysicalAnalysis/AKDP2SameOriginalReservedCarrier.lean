import AKCX29ActualSourceAllSpatialGraphs
import AKBV6DiagonalGraphOriginalCore
import AKBZ30ActualFullDerivativeOneHigh

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.ActualOriginalSourceMoments Grad.ActualOriginalSourceFirst Grad.WeightedJets.Ordered
open Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.OriginalCartesianTameEstimate Grad.WeakTesting.Commutation

/-- The all-order original source carrier uses precisely the closed
weighted derivative occurring in the BZ30 quantitative input. -/
theorem originalSourceOrderedJoint_coordinate {dimension : ℕ}
    (parameters : PhaseParameters) (core : ACore parameters dimension)
    (rank : ℕ) (word : CartesianWord rank) (cell : ℤ) :
    fieldCellProjection dimension openUnitDisk cell (originalSourceOrderedJoint parameters core rank word) =
      originalSourceOrderedCoordinate parameters core rank word cell := by
  apply Lp.ext
  filter_upwards [fieldCellProjection_ae dimension openUnitDisk
      (originalSourceOrderedJoint parameters core rank word),
    originalSourceOrderedJoint_same parameters core rank word,
    originalSourceOrderedCoordinate_same parameters core rank word cell] with point projected same closed
  exact (projected cell).trans ((same cell).trans closed.symm)

/-- Weak uniqueness identifies every stored derivative of a graph with
the SAME original core, rather than merely proving existence of a core. -/
theorem startupRecoveredDerivative_originalCore {dimension order weight : ℕ}
    (parameters : PhaseParameters) (core : ACore parameters dimension)
    (jet : GraphGrade dimension order weight openUnitDisk)
    (same : base dimension order openUnitDisk (fun _ => weight) jet = (originalSourceMoments parameters core).field)
    (index : JetIndex order) :
    Realization.recoveredDerivative dimension order openUnitDisk (fun _ => weight) index jet =
      originalSourceOrderedJoint parameters core (degree index) (derivativeWord index) := by
  have actual := recoveredDerivative_hasWeak dimension order openUnitDisk (fun _ => weight) index jet
  have original : HasWeakOrderedDerivative dimension openUnitDisk (degree index) (derivativeWord index)
      (base dimension order openUnitDisk (fun _ => weight) jet)
      (originalSourceOrderedJoint parameters core (degree index) (derivativeWord index)) := by
    rw [same]
    exact originalSourceOrderedJoint_weak parameters core (degree index) (derivativeWord index)
  exact weakEquality dimension openUnitDisk openUnitDisk_isOpen (degree index) (derivativeWord index)
    (derivativeWord index) (fun _ => rfl) _ _ _ actual original

/-- Exact input-reserve cancellation into the literal BZ30 original
carrier. This identifies all signed cells and all spatial derivatives. -/
theorem startupReservedDerivative_originalCarrier {dimension order weight reserve : ℕ}
    (parameters : PhaseParameters) {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (core : ACore parameters dimension)
    (jet : GraphGrade dimension order weight openUnitDisk)
    (same : base dimension order openUnitDisk (fun _ => weight) jet = (originalSourceMoments parameters core).field)
    (bound : reserve≤weight) (index : JetIndex order) :
    startupReservedDerivative admissible bound index jet =
      originalMixedDerivativeCarrier parameters admissible core (degree index) reserve (derivativeWord index) := by
  apply (Grad.FullCellKernel.coordinateIsometry dimension openUnitDisk).injective
  apply lp.ext
  funext cell
  change fieldCellProjection dimension openUnitDisk cell (startupReservedDerivative admissible bound index jet) =
    fieldCellProjection dimension openUnitDisk cell (originalMixedDerivativeCarrier parameters admissible core (degree index) reserve (derivativeWord index))
  rw [startupReservedDerivative_projection,startupRecoveredDerivative_originalCore parameters core jet same index,
    originalSourceOrderedJoint_coordinate,originalMixedDerivativeCarrier_coordinate]
  simp only [originalMixedDerivativeCoordinate,originalSourceOrderedCoordinate,Complex.ofReal_pow]

end Grad.CartesianStartup
