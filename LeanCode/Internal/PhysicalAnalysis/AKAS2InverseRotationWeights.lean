import AKAP6OriginalB10LocalizedRowsConsumer
import AKAS1InverseCovectorDistribution

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000

open MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- Literal inverse rotation entry; the minus angle is not omitted. -/
def startupInverseRotationEntry (direction coordinate : Fin 2) (angle : ℝ) : ℝ :=
  planeRotation (-angle) (spatialDirection direction) coordinate

theorem startupInverseRotationEntry_eq (direction coordinate : Fin 2) (angle : ℝ) :
    startupInverseRotationEntry direction coordinate angle =
      (planeRotationEquiv angle).symm (spatialDirection direction) coordinate := rfl

theorem startupInverseRotationEntry_smooth (direction coordinate : Fin 2) :
    ContDiff ℝ ∞ (startupInverseRotationEntry direction coordinate) := by
  change ContDiff ℝ ∞ (fun angle : ℝ => planeRotation (-angle) (spatialDirection direction) coordinate)
  fin_cases direction <;> fin_cases coordinate <;>
    simp [planeRotation, spatialDirection] <;> fun_prop

theorem startupInverseRotationEntry_bound (direction coordinate : Fin 2) (angle : ℝ) :
    ‖startupInverseRotationEntry direction coordinate angle‖ ≤ 1 :=
  orthogonal_entry_bound (planeRotationEquiv angle).symm direction coordinate

def startupCovectorWeight (weight : ℝ → ℂ) (direction coordinate : Fin 2) (angle : ℝ) : ℂ :=
  weight angle * (startupInverseRotationEntry direction coordinate angle : ℂ)

theorem startupCovectorWeight_smooth (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (direction coordinate : Fin 2) : ContDiff ℝ ∞ (startupCovectorWeight weight direction coordinate) := by
  exact smooth.mul (Complex.ofRealCLM.contDiff.comp (startupInverseRotationEntry_smooth direction coordinate))

theorem startupCovectorWeight_bound (weight : ℝ → ℂ) (direction coordinate : Fin 2) (angle : ℝ) :
    ‖startupCovectorWeight weight direction coordinate angle‖ ≤ ‖weight angle‖ := by
  rw [startupCovectorWeight, norm_mul, Complex.norm_real]
  exact (mul_le_mul_of_nonneg_left (startupInverseRotationEntry_bound direction coordinate angle)
    (norm_nonneg (weight angle))).trans_eq (mul_one _)

/-- Actual full-cell disk kernel carrying the correct input covector. -/
def startupCovectorAngularKernel (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (direction coordinate : Fin 2) : StartupL2 3 →L[ℂ] StartupL2 3 :=
  startupAngularKernel 3 (startupCovectorWeight weight direction coordinate)
    (startupCovectorWeight_smooth weight smooth direction coordinate)

def startupCovectorAngularFirst (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (direction coordinate : Fin 2) : StartupFirst 3 →L[ℂ] StartupFirst 3 :=
  startupAngularFirstGraph 3 (startupCovectorWeight weight direction coordinate)
    (startupCovectorWeight_smooth weight smooth direction coordinate)

theorem startupCovectorAngular_compatible (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (direction coordinate : Fin 2) :
    StartupCompatible (startupCovectorAngularKernel weight smooth direction coordinate)
      (startupCovectorAngularFirst weight smooth direction coordinate) :=
  startupAngularFirstGraph_compatible 3 (startupCovectorWeight weight direction coordinate)
    (startupCovectorWeight_smooth weight smooth direction coordinate)

end Grad.CartesianStartup
