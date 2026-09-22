import AKCX25SameOriginalMixedPrincipal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open MeasureTheory
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.Ordered Grad.WeakTesting Grad.WeakTesting.Commutation
open Grad.RepresentedKernel.SpatialProduct

def startupListDerivativeTest (directions : List (Fin 2)) (test : TestFunction openUnitDisk) : TestFunction openUnitDisk :=
  directions.foldr startupDerivativeTest test

theorem startupListDerivativeTest_toFun (directions : List (Fin 2)) (test : TestFunction openUnitDisk) :
    (startupListDerivativeTest directions test).toFun = Grad.WeakTesting.Commutation.listDerivative directions test.toFun := by
  induction directions with
  | nil => rfl
  | cons direction rest ih =>
    change directionDerivative direction (startupListDerivativeTest rest test).toFun =
      differentiate direction (Grad.WeakTesting.Commutation.listDerivative rest test.toFun)
    rw [ih]
    rfl

theorem startupListDerivativeTest_commute (directions : List (Fin 2)) (direction : Fin 2) (test : TestFunction openUnitDisk) :
    startupListDerivativeTest directions (startupDerivativeTest direction test) =
      startupDerivativeTest direction (startupListDerivativeTest directions test) := by
  induction directions with
  | nil => rfl
  | cons first rest ih =>
    change startupDerivativeTest first (startupListDerivativeTest rest (startupDerivativeTest direction test)) = _
    rw [ih,startupDerivativeTest_commute first direction]
    rfl

theorem startupListDerivativeTest_add (directions : List (Fin 2)) (first second : TestFunction openUnitDisk) :
    startupListDerivativeTest directions (startupAddTest first second) =
      startupAddTest (startupListDerivativeTest directions first) (startupListDerivativeTest directions second) := by
  induction directions with
  | nil => rfl
  | cons direction rest ih =>
    change startupDerivativeTest direction (startupListDerivativeTest rest (startupAddTest first second)) = _
    rw [ih,startupDerivativeTest_add]
    rfl

theorem startupListDerivativeTest_laplacian (directions : List (Fin 2)) (test : TestFunction openUnitDisk) :
    startupListDerivativeTest directions (startupLaplacianTest test) =
      startupLaplacianTest (startupListDerivativeTest directions test) := by
  unfold startupLaplacianTest
  rw [startupListDerivativeTest_add]
  simp only [startupListDerivativeTest_commute]

theorem startupOrderedDerivative_pairing {order rank weight : ℕ}
    (field : GraphGrade 3 order weight openUnitDisk) (bound : rank ≤ order)
    (word : Fin rank → Fin 2) (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) :
    startupTestPairing cell vector test
      (orderedDerivative 3 order rank openUnitDisk (fun _ => weight) bound field word) =
      (-1 : ℂ)^rank * startupTestPairing cell vector
        (startupListDerivativeTest (List.ofFn word) test) (base 3 order openUnitDisk (fun _ => weight) field) := by
  rw [startupTestPairing_apply,startupTestPairing_apply,startupListDerivativeTest_toFun]
  rw [listDerivative_ofFn _ _ _ test.smooth]
  exact orderedDerivative_integral 3 order rank openUnitDisk (fun _ => weight) bound field word
    cell vector test.toFun test.smooth test.compact test.supported

end Grad.CartesianStartup
