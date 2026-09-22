import AKBP8SamePhaseDivDivEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.Ordered
open Grad.WeakTesting Grad.WeakTesting.Commutation Grad.RepresentedKernel.SpatialProduct
open Grad.GaugeCoefficients.Physical.RadialLedger

def startupFirstDerivative (field : StartupFirst 3) (direction : Fin 2) : StartupL2 3 :=
  orderedDerivative 3 1 1 openUnitDisk (fun _ => 0) le_rfl field (startupFirstWord direction)

theorem startupOrderedFirst_direction (direction : Fin 2) (test : Spatial → ℝ) :
    orderedTestDerivative 1 (startupFirstWord direction) test = directionDerivative direction test := by
  funext point
  rw [orderedTestDerivative,iteratedFDeriv_one_apply]
  rfl

/-- A genuine known first graph supplies its actual derivative L2 field. No
first graph of the rough unknown is used to pay a source derivative. -/
theorem startupFirstGraph_pairing (field : StartupFirst 3) (cell : ℤ) (vector : PhysicalValue 3)
    (test : TestFunction openUnitDisk) (direction : Fin 2) :
    startupTestPairing cell vector test (startupFirstDerivative field direction) =
      -startupTestPairing cell vector (startupDerivativeTest direction test) (base 3 1 openUnitDisk (fun _ => 0) field) := by
  have weak := orderedDerivative_hasWeak 3 1 1 openUnitDisk (fun _ => 0) le_rfl field (startupFirstWord direction)
  have identity := (hasWeakOrderedDerivative_iff_integral 3 openUnitDisk 1 (startupFirstWord direction)
    (base 3 1 openUnitDisk (fun _ => 0) field) (startupFirstDerivative field direction)).mp weak
      cell vector test.toFun test.smooth test.compact test.supported
  rw [startupOrderedFirst_direction,pow_one,neg_one_mul] at identity
  simpa only [startupTestPairing_apply,startupDerivativeTest] using identity

/-- Known tensor rows in the first graph are only a first-order remainder in
the elliptic equation, using their literal weak derivatives. -/
theorem startupKnownFirstTensor_absorb (field zeroth : StartupL2 3)
    (tensor : Fin 2 → Fin 2 → StartupL2 3) (known : Fin 2 → Fin 2 → StartupFirst 3)
    (flux : Fin 2 → StartupL2 3)
    (equation : StartupWeakDivDivEquation field zeroth
      (fun outer inner => tensor outer inner + base 3 1 openUnitDisk (fun _ => 0) (known outer inner)) flux) :
    StartupWeakDivDivEquation field zeroth tensor
      (fun direction => flux direction - ∑ outer : Fin 2, startupFirstDerivative (known outer direction) outer) := by
  intro cell vector test
  have identity := equation cell vector test
  have knownWeak (outer inner : Fin 2) :=
    startupFirstGraph_pairing (known outer inner) cell vector (startupDerivativeTest inner test) outer
  simp only [Fin.sum_univ_two,map_add,map_sub] at identity ⊢
  have first := knownWeak 0 0
  have second := knownWeak 0 1
  have third := knownWeak 1 0
  have fourth := knownWeak 1 1
  linear_combination identity + first + second + third + fourth

end Grad.CartesianStartup
