import AJE12RealKnownOperatorCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.AnnularKernelOrbit Grad.AnnularHighInverseOrbit

/-- A genuine full two-parameter derivative tower, with each derivative
identity retained before specializing its possibly large source carrier. -/
structure RealOrbitTower (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  jet : ℕ → ℕ → OrbitParameter → E
  derivative : ∀ angular cell tau, HasFDerivAt (jet angular cell)
    (orbitColumns (jet (angular + 1) cell tau) (jet angular (cell + 1) tau)) tau

namespace RealOrbitTower
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

def map (tower : RealOrbitTower E) (mapping : E →L[ℝ] F) : RealOrbitTower F where
  jet angular cell tau := mapping (tower.jet angular cell tau)
  derivative angular cell tau := mappedOrbit_hasFDerivAt mapping _ _ _ tau (tower.derivative angular cell tau)

theorem smooth (tower : RealOrbitTower E) (angular cell : ℕ) : ContDiff ℝ ∞ (tower.jet angular cell) :=
  orbitTower_contDiff tower.jet tower.derivative angular cell

theorem map_bound (tower : RealOrbitTower E) (mapping : E →L[ℝ] F)
    (contractive : ∀ value, ‖mapping value‖ ≤ ‖value‖) (angular cell : ℕ) (tau : OrbitParameter) :
    ‖(tower.map mapping).jet angular cell tau‖ ≤ ‖tower.jet angular cell tau‖ :=
  contractive (tower.jet angular cell tau)

end RealOrbitTower
end Grad.AnnularStrongOrbit
