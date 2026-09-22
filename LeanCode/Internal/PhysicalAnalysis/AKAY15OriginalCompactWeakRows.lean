import AKAY14SameFieldDivDivH1

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set MeasureTheory

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.WeightedJets

/-- The genuine compact-test pairing of one raw complex component. The raw
representatives need only the integrability proved by the axis-removal adapter. -/
def startupRawPairing (field : ℤ → Spatial → ℂ) (cell : ℤ)
    (test : TestFunction openUnitDisk) : ℂ :=
  ∫ point in openUnitDisk, test.toFun point • field cell point

def startupMeanTest (test : TestFunction openUnitDisk) : TestFunction openUnitDisk :=
  startupAngularCompactTest (fun _ : ℝ => 1) contDiff_const test

def startupMeanFreeTest (test : TestFunction openUnitDisk) : TestFunction openUnitDisk :=
  startupSubTest test (startupMeanTest test)

/-- Literal original first-order equations, entirely on genuine real compact
unit-disk tests. This interface is valid before Cartesian H1 or smoothness.
The determinant row retains its outer mean removal and its original signs.
The caller supplies the original axial symbol; dilation replaces it by ell times
that symbol, with Theta divided by ell and the determinant source multiplied by ell. -/
structure StartupOriginalCompactWeakRows (axial : ℤ → ℂ)
    (theta : ℤ → Spatial → ℂ) (vector : Fin 2 → ℤ → Spatial → ℂ)
    (scalar : ℤ → Spatial → ℂ)
    (force correctionA quarterVector : Fin 2 → ℤ → Spatial → ℂ)
    (third correctionC determinant : ℤ → Spatial → ℂ)
    (planarFlux : Fin 2 → ℤ → Spatial → ℂ) (scalarFlux : ℤ → Spatial → ℂ) : Prop where
  forceEquation : ∀ (cell : ℤ) (coordinate : Fin 2) (test : TestFunction openUnitDisk),
    startupRawPairing (force coordinate) cell test - startupRawPairing (correctionA coordinate) cell test =
      startupRawPairing theta cell (startupRotationTest (startupDerivativeTest coordinate test)) +
      startupRawPairing (vector coordinate) cell (startupRotationTest test) -
      startupRawPairing (quarterVector coordinate) cell test
  thirdEquation : ∀ (cell : ℤ) (test : TestFunction openUnitDisk),
    startupRawPairing third cell test + startupRawPairing correctionC cell test =
      -startupRawPairing scalar cell (startupRotationTest test) +
      axial cell * startupRawPairing theta cell (startupRotationTest test)
  determinantEquation : ∀ (cell : ℤ) (test : TestFunction openUnitDisk),
    startupRawPairing determinant cell test =
      (∑ coordinate : Fin 2, startupRawPairing (vector coordinate) cell
        (startupDerivativeTest coordinate (startupMeanFreeTest test))) -
      axial cell * startupRawPairing scalar cell (startupMeanFreeTest test) -
      (∑ coordinate : Fin 2, startupRawPairing (planarFlux coordinate) cell
        (startupDerivativeTest coordinate (startupMeanFreeTest test))) +
      axial cell * startupRawPairing scalarFlux cell (startupMeanFreeTest test)

/-- The scalar gauges needed in elimination are distributional mean-zero
identities, not regularity assumptions on Theta or the quotient's third component. -/
structure StartupOriginalCompactScalarGauges (theta scalar : ℤ → Spatial → ℂ) : Prop where
  thetaMean : ∀ (cell : ℤ) (test : TestFunction openUnitDisk),
    startupRawPairing theta cell (startupMeanTest test) = 0
  scalarMean : ∀ (cell : ℤ) (test : TestFunction openUnitDisk),
    startupRawPairing scalar cell (startupMeanTest test) = 0

end Grad.CartesianStartup
