import BKB33FixedFourierKernels

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Ledger

def coordinateProjectionKernel (parameters : PhaseParameters) (dimension : ℕ)
    (coordinate : Fin dimension) :
    FullTwoFrequencyKernel parameters dimension 1 :=
  constantMatrixKernel parameters dimension 1 (matrixUnit 0 coordinate)

def coordinateInjectionKernel (parameters : PhaseParameters) (dimension : ℕ)
    (coordinate : Fin dimension) :
    FullTwoFrequencyKernel parameters 1 dimension :=
  constantMatrixKernel parameters 1 dimension (matrixUnit coordinate 0)

def componentModeKernel (parameters : PhaseParameters) (dimension : ℕ)
    (coordinate : Fin dimension) (multiplier : ℤ × ℤ → ℂ)
    (bound : ℝ) (bounded : ∀ input, ‖multiplier input‖ ≤ bound) :
    FullTwoFrequencyKernel parameters dimension dimension :=
  fullKernelComposition (coordinateInjectionKernel parameters dimension coordinate)
    (fullKernelComposition
      (scalarModeDiagonalKernel parameters 1 multiplier bound bounded)
      (coordinateProjectionKernel parameters dimension coordinate))

def angularMeanComponentKernel (parameters : PhaseParameters) (dimension : ℕ)
    (coordinate : Fin dimension) :
    FullTwoFrequencyKernel parameters dimension dimension :=
  componentModeKernel parameters dimension coordinate angularMeanMultiplier 1
    angularMeanMultiplier_norm_le

def angularMeanFreeComponentKernel (parameters : PhaseParameters) (dimension : ℕ)
    (coordinate : Fin dimension) :
    FullTwoFrequencyKernel parameters dimension dimension :=
  componentModeKernel parameters dimension coordinate angularMeanFreeMultiplier 1
    angularMeanFreeMultiplier_norm_le

def angularInverseComponentKernel (parameters : PhaseParameters) (dimension : ℕ)
    (coordinate : Fin dimension) :
    FullTwoFrequencyKernel parameters dimension dimension :=
  componentModeKernel parameters dimension coordinate angularInverseMultiplier 1
    angularInverseMultiplier_norm_le

def angularDoubleInverseComponentKernel (parameters : PhaseParameters) (dimension : ℕ)
    (coordinate : Fin dimension) :
    FullTwoFrequencyKernel parameters dimension dimension :=
  componentModeKernel parameters dimension coordinate angularDoubleInverseMultiplier 1
    angularDoubleInverseMultiplier_norm_le

/-- AE14's literal decoding `(x0,Y,C) ↦ (x0,K²Y,KC)`, extended by
the exact support projections to the ambient three-component trace. -/
def encodedJKernel (parameters : PhaseParameters) :
    FullTwoFrequencyKernel parameters 3 3 :=
  fullKernelAdd (angularMeanComponentKernel parameters 3 0)
    (fullKernelAdd (angularDoubleInverseComponentKernel parameters 3 1)
      (angularInverseComponentKernel parameters 3 2))

/-- AE16's encoded angular derivative `(x0,Y,C) ↦ (0,KY,C)`. -/
def encodedRotationKernel (parameters : PhaseParameters) :
    FullTwoFrequencyKernel parameters 3 3 :=
  fullKernelAdd (angularInverseComponentKernel parameters 3 1)
    (angularMeanFreeComponentKernel parameters 3 2)

def tailInjectionMap : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 3 :=
  matrixUnit 1 0 + matrixUnit 2 1

def tailInjectionKernel (parameters : PhaseParameters) :
    FullTwoFrequencyKernel parameters 2 3 :=
  constantMatrixKernel parameters 2 3 tailInjectionMap

def firstCoordinateInjectionKernel (parameters : PhaseParameters) :
    FullTwoFrequencyKernel parameters 1 3 :=
  coordinateInjectionKernel parameters 3 0

def secondCoordinateInjectionKernel (parameters : PhaseParameters) :
    FullTwoFrequencyKernel parameters 1 3 :=
  coordinateInjectionKernel parameters 3 1

def thirdCoordinateInjectionKernel (parameters : PhaseParameters) :
    FullTwoFrequencyKernel parameters 1 3 :=
  coordinateInjectionKernel parameters 3 2

def sevenInputSlotKernel (parameters : PhaseParameters) (slot : Fin 7) :
    FullTwoFrequencyKernel parameters 7 1 :=
  coordinateProjectionKernel parameters 7 slot

def diagonalThreeMap (first second third : ℂ) :
    ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 3 :=
  first • matrixUnit 0 0 + second • matrixUnit 1 1 + third • matrixUnit 2 2

def encodedD0Kernel (parameters : PhaseParameters) :
    FullTwoFrequencyKernel parameters 3 3 :=
  constantMatrixKernel parameters 3 3 (diagonalThreeMap (-2) (-1) 1)

def encodedD0InverseKernel (parameters : PhaseParameters) :
    FullTwoFrequencyKernel parameters 3 3 :=
  constantMatrixKernel parameters 3 3 (diagonalThreeMap (-(2 : ℂ)⁻¹) (-1) 1)

end Grad.BoundaryKernelAction
