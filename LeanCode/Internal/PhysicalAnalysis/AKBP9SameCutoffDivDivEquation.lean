import AKBP8SamePhaseDivDivEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.SpatialMultiplier Grad.RepresentedKernel.SpatialProduct

variable (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff)

def startupCutoffDerivative (direction : Fin 2) : StartupL2 3 →L[ℂ] StartupL2 3 :=
  startupCutoffL2 (directionDerivative direction cutoff) (startupTestDerivative_smooth cutoff smooth direction)
    (startupTestDerivative_compact cutoff compact direction)

def startupCutoffSecondDerivative (outer inner : Fin 2) : StartupL2 3 →L[ℂ] StartupL2 3 :=
  startupCutoffL2 (directionDerivative outer (directionDerivative inner cutoff))
    (startupTestDerivative_smooth _ (startupTestDerivative_smooth cutoff smooth inner) outer)
    (startupTestDerivative_compact _ (startupTestDerivative_compact cutoff compact inner) outer)

theorem startupCutoffL2_first_test (field : StartupL2 3) (cell : ℤ) (vector : PhysicalValue 3)
    (test : TestFunction openUnitDisk) (direction : Fin 2) :
    startupTestPairing cell vector (startupDerivativeTest direction (multiplyTest cutoff smooth test)) field =
      startupTestPairing cell vector test (startupCutoffDerivative cutoff smooth compact direction field) +
      startupTestPairing cell vector (startupDerivativeTest direction test) (startupCutoffL2 cutoff smooth compact field) := by
  rw [startupDerivativeTest_multiply,startupTestPairing_add,add_apply]
  simp only [startupCutoffDerivative,startupCutoffL2_pairing]

def startupCutoffEquationZeroth (field zeroth : StartupL2 3)
    (tensor : Fin 2 → Fin 2 → StartupL2 3) (flux : Fin 2 → StartupL2 3) : StartupL2 3 :=
  startupCutoffL2 cutoff smooth compact zeroth +
    (∑ outer : Fin 2, ∑ inner : Fin 2, startupCutoffSecondDerivative cutoff smooth compact outer inner (tensor outer inner)) +
    (∑ direction : Fin 2, startupCutoffDerivative cutoff smooth compact direction (flux direction)) -
    ∑ direction : Fin 2, startupCutoffSecondDerivative cutoff smooth compact direction direction field

def startupCutoffEquationFlux (field : StartupL2 3)
    (tensor : Fin 2 → Fin 2 → StartupL2 3) (flux : Fin 2 → StartupL2 3) (direction : Fin 2) : StartupL2 3 :=
  startupCutoffL2 cutoff smooth compact (flux direction) +
    (∑ inner : Fin 2, startupCutoffDerivative cutoff smooth compact inner (tensor direction inner)) +
    (∑ outer : Fin 2, startupCutoffDerivative cutoff smooth compact outer (tensor outer direction)) -
    (2 : ℂ) • startupCutoffDerivative cutoff smooth compact direction field

/-- Exact interior localization of the same rough div-div equation. Every
new term contains a genuine cutoff derivative and an L2 field; no derivative
of the rough input or coefficient has been inserted. -/
theorem startupSame_cutoff_divDiv (field zeroth : StartupL2 3)
    (tensor : Fin 2 → Fin 2 → StartupL2 3) (flux : Fin 2 → StartupL2 3)
    (equation : StartupWeakDivDivEquation field zeroth tensor flux) :
    StartupWeakDivDivEquation (startupCutoffL2 cutoff smooth compact field)
      (startupCutoffEquationZeroth cutoff smooth compact field zeroth tensor flux)
      (fun outer inner => startupCutoffL2 cutoff smooth compact (tensor outer inner))
      (startupCutoffEquationFlux cutoff smooth compact field tensor flux) := by
  intro cell vector test
  have transformed := equation cell vector (multiplyTest cutoff smooth test)
  simp only [startupLaplacianTest,startupTestPairing_add,add_apply] at transformed
  rw [startupCutoffL2_second_test cutoff smooth compact cell vector test field 0 0,
    startupCutoffL2_second_test cutoff smooth compact cell vector test field 1 1] at transformed
  have tensorTransfer (outer inner : Fin 2) :=
    startupCutoffL2_second_test cutoff smooth compact cell vector test (tensor outer inner) outer inner
  have fluxTransfer (direction : Fin 2) :=
    startupCutoffL2_first_test cutoff smooth compact (flux direction) cell vector test direction
  simp_rw [tensorTransfer,fluxTransfer] at transformed
  rw [← startupCutoffL2_pairing cutoff smooth compact cell vector test zeroth] at transformed
  simp only [startupLaplacianTest,startupTestPairing_add,add_apply,startupCutoffEquationZeroth,startupCutoffEquationFlux,
    startupCutoffDerivative,startupCutoffSecondDerivative,Fin.sum_univ_two,map_add,map_sub,map_smul,smul_eq_mul] at transformed ⊢
  linear_combination transformed

end Grad.CartesianStartup
