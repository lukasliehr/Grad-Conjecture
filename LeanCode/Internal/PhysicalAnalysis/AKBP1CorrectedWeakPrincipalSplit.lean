import AKBL6SameOriginalWeakEllipticRows
import AKAY30GenuinePrincipalWeakConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets

/-- Literal corrected principal planar row; its force sign follows right=F-a. -/
def startupERPlanarPrincipal (force flux : StartupL2 2) (cell : ℤ)
    (coordinate : Fin 2) (test : TestFunction openUnitDisk) : ℂ :=
  if coordinate = 0 then
    -startupWeakDivergencePairing flux cell (startupDerivativeTest 0 test) +
      startupWeakCurlPairing force cell (startupTrueInverseTest (startupDerivativeTest 1 test)) -
      (2 : ℂ) * startupWeakDivergencePairing flux cell (startupTrueInverseTest (startupDerivativeTest 1 test))
  else -startupWeakDivergencePairing flux cell (startupDerivativeTest 1 test) -
      startupWeakCurlPairing force cell (startupTrueInverseTest (startupDerivativeTest 0 test)) +
      (2 : ℂ) * startupWeakDivergencePairing flux cell (startupTrueInverseTest (startupDerivativeTest 0 test))

/-- The determinant's remaining divergence, with the genuine equivariant
source term retained. Axial multiplication is explicit at each cell. -/
def startupERLowerDivergence (axial : ℤ → ℂ) (scalar determinant scalarFlux : StartupL2 1)
    (source : StartupL2 2) (cell : ℤ) (test : TestFunction openUnitDisk) : ℂ :=
  -startupCoordinateTestPairing cell 0 test determinant -
    axial cell * startupCoordinateTestPairing cell 0 test scalar +
    axial cell * startupCoordinateTestPairing cell 0 test scalarFlux +
    startupWeakDivergencePairing ((1/2 : ℂ) • originalValueKernel quarterValueMap
      (originalAverageKernel source)) cell test

def startupERPlanarRemainder (lower : TestFunction openUnitDisk → ℂ)
    (source : StartupL2 2) (cell : ℤ) (coordinate : Fin 2)
    (test : TestFunction openUnitDisk) : ℂ :=
  if coordinate = 0 then
    -lower (startupDerivativeTest 0 test) -
      startupWeakCurlPairing source cell (startupTrueInverseTest (startupDerivativeTest 1 test)) -
      (2 : ℂ) * lower (startupTrueInverseTest (startupDerivativeTest 1 test))
  else -lower (startupDerivativeTest 1 test) +
      startupWeakCurlPairing source cell (startupTrueInverseTest (startupDerivativeTest 0 test)) +
      (2 : ℂ) * lower (startupTrueInverseTest (startupDerivativeTest 0 test))

/-- Exact ER principal/lower split from the already derived weak second-order
rows. This is algebra on SAME rough fields; no missing derivative is assumed. -/
theorem startupERPlanar_split (vector source force flux : StartupL2 2)
    (lower : ℤ → TestFunction openUnitDisk → ℂ)
    (divergence : ∀ cell test, startupWeakDivergencePairing vector cell test =
      startupWeakDivergencePairing flux cell test + lower cell test)
    (laplacian : ∀ cell coordinate test,
      startupCoordinateTestPairing cell coordinate (startupLaplacianTest test) vector =
        if coordinate = 0 then
          -startupWeakDivergencePairing vector cell (startupDerivativeTest 0 test) -
            startupWeakCurlPairing (source-force) cell (startupTrueInverseTest (startupDerivativeTest 1 test)) -
            (2 : ℂ) * startupWeakDivergencePairing vector cell (startupTrueInverseTest (startupDerivativeTest 1 test))
        else -startupWeakDivergencePairing vector cell (startupDerivativeTest 1 test) +
            startupWeakCurlPairing (source-force) cell (startupTrueInverseTest (startupDerivativeTest 0 test)) +
            (2 : ℂ) * startupWeakDivergencePairing vector cell (startupTrueInverseTest (startupDerivativeTest 0 test)))
    (cell : ℤ) (coordinate : Fin 2) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell coordinate (startupLaplacianTest test) vector =
      startupERPlanarPrincipal force flux cell coordinate test +
      startupERPlanarRemainder (lower cell) source cell coordinate test := by
  rw [laplacian]
  simp only [divergence, startupWeakCurl_sub_field, startupERPlanarPrincipal, startupERPlanarRemainder]
  split_ifs <;> ring

end Grad.CartesianStartup
