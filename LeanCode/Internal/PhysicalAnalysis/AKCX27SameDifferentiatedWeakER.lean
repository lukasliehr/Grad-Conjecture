import AKCX26ActualOrderedWeakTests

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.WeightedJets.Ordered

/-- Differentiate the actual rough ER identity using only the already
available spatial graphs. The exact tensor and flux derivatives remain in
the equation; no commutation through a variable coefficient is asserted. -/
theorem startupSame_ordered_weakDivDiv {order rank weight : ℕ}
    (field zeroth : GraphGrade 3 order weight openUnitDisk)
    (tensor : Fin 2 → Fin 2 → GraphGrade 3 order weight openUnitDisk)
    (flux : Fin 2 → GraphGrade 3 order weight openUnitDisk)
    (equation : StartupWeakDivDivEquation
      (base 3 order openUnitDisk (fun _ => weight) field)
      (base 3 order openUnitDisk (fun _ => weight) zeroth)
      (fun outer inner => base 3 order openUnitDisk (fun _ => weight) (tensor outer inner))
      (fun direction => base 3 order openUnitDisk (fun _ => weight) (flux direction)))
    (bound : rank ≤ order) (word : Fin rank → Fin 2) :
    StartupWeakDivDivEquation
      (orderedDerivative 3 order rank openUnitDisk (fun _ => weight) bound field word)
      (orderedDerivative 3 order rank openUnitDisk (fun _ => weight) bound zeroth word)
      (fun outer inner => orderedDerivative 3 order rank openUnitDisk (fun _ => weight) bound (tensor outer inner) word)
      (fun direction => orderedDerivative 3 order rank openUnitDisk (fun _ => weight) bound (flux direction) word) := by
  intro cell vector test
  simp only [startupOrderedDerivative_pairing,startupListDerivativeTest_laplacian,startupListDerivativeTest_commute]
  simpa only [Fin.sum_univ_two,mul_add] using congrArg (fun value : ℂ => (-1 : ℂ)^rank * value)
    (equation cell vector (startupListDerivativeTest (List.ofFn word) test))

end Grad.CartesianStartup
