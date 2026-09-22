import AKBP7SameOriginalPhaseWeakTransfer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.AnalyticWeights.Calculus Grad.WeightedJets.SpatialMultiplier

/-- A compact disk identity on the full integer-cell carrier. Flux pairings
carry their test-derivative sign explicitly until distributional conversion. -/
def StartupWeakDivDivEquation (field zeroth : StartupL2 3)
    (tensor : Fin 2 → Fin 2 → StartupL2 3) (flux : Fin 2 → StartupL2 3) : Prop :=
  ∀ cell vector test, startupTestPairing cell vector (startupLaplacianTest test) field =
    (∑ outer : Fin 2, ∑ inner : Fin 2,
      startupTestPairing cell vector (startupDerivativeTest outer (startupDerivativeTest inner test)) (tensor outer inner)) +
    startupTestPairing cell vector test zeroth +
    ∑ direction : Fin 2, startupTestPairing cell vector (startupDerivativeTest direction test) (flux direction)

def startupPhaseEquationZeroth (sigma gamma ell : ℝ) (nonnegative : 0 ≤ gamma)
    (ellNonnegative : 0 ≤ ell) (ellOne : ell ≤ 1) (zeroth fieldSecond : StartupL2 3)
    (tensorSecond : Fin 2 → Fin 2 → StartupL2 3) (fluxFirst : Fin 2 → StartupL2 3) : StartupL2 3 :=
  zeroth + (∑ outer : Fin 2, ∑ inner : Fin 2,
    startupScaledPhaseSecondField sigma gamma ell nonnegative ellNonnegative ellOne outer inner (tensorSecond outer inner)) +
  (∑ direction : Fin 2, startupScaledPhaseFirstField sigma gamma ell nonnegative ellNonnegative ellOne direction (fluxFirst direction)) -
  ∑ direction : Fin 2, startupScaledPhaseSecondField sigma gamma ell nonnegative ellNonnegative ellOne direction direction fieldSecond

def startupPhaseEquationFlux (sigma gamma ell : ℝ) (nonnegative : 0 ≤ gamma)
    (ellNonnegative : 0 ≤ ell) (ellOne : ell ≤ 1) (fieldFirst : StartupL2 3)
    (tensorFirst : Fin 2 → Fin 2 → StartupL2 3) (flux : Fin 2 → StartupL2 3) (direction : Fin 2) : StartupL2 3 :=
  flux direction +
    (∑ inner : Fin 2, startupScaledPhaseFirstField sigma gamma ell nonnegative ellNonnegative ellOne inner (tensorFirst direction inner)) +
    (∑ outer : Fin 2, startupScaledPhaseFirstField sigma gamma ell nonnegative ellNonnegative ellOne outer (tensorFirst outer direction)) -
    (2 : ℂ) • startupScaledPhaseFirstField sigma gamma ell nonnegative ellNonnegative ellOne direction fieldFirst

/-- Exact phase conjugation of the rough divergence-form equation. The
principal tensor is unchanged; all first/Hessian phase remainders are literal
L2 fields paid by SAME output-cell moments, with no coefficient commutation. -/
theorem startupSame_phase_divDiv (sigma gamma ell : ℝ) (nonnegative : 0 ≤ gamma)
    (ellNonnegative : 0 ≤ ell) (ellOne : ell ≤ 1)
    (field rawField zeroth rawZeroth fieldFirst fieldSecond : StartupL2 3)
    (tensor rawTensor tensorFirst tensorSecond : Fin 2 → Fin 2 → StartupL2 3)
    (flux rawFlux fluxFirst : Fin 2 → StartupL2 3)
    (fieldSame : StartupRadialRelated (physicalWeight sigma gamma ell) field rawField)
    (zeroSame : StartupRadialRelated (physicalWeight sigma gamma ell) zeroth rawZeroth)
    (tensorSame : ∀ outer inner, StartupRadialRelated (physicalWeight sigma gamma ell) (tensor outer inner) (rawTensor outer inner))
    (fluxSame : ∀ direction, StartupRadialRelated (physicalWeight sigma gamma ell) (flux direction) (rawFlux direction))
    (fieldFirstSame : StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell) fieldFirst field)
    (fieldSecondSame : StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell ^ 2) fieldSecond field)
    (tensorFirstSame : ∀ outer inner, StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell)
      (tensorFirst outer inner) (tensor outer inner))
    (tensorSecondSame : ∀ outer inner, StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell ^ 2)
      (tensorSecond outer inner) (tensor outer inner))
    (fluxFirstSame : ∀ direction, StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell)
      (fluxFirst direction) (flux direction))
    (equation : StartupWeakDivDivEquation rawField rawZeroth rawTensor rawFlux) :
    StartupWeakDivDivEquation field
      (startupPhaseEquationZeroth sigma gamma ell nonnegative ellNonnegative ellOne zeroth fieldSecond tensorSecond fluxFirst)
      tensor (startupPhaseEquationFlux sigma gamma ell nonnegative ellNonnegative ellOne fieldFirst tensorFirst flux) := by
  intro cell vector test
  have transformed := equation cell vector
    (multiplyTest (physicalWeight sigma gamma ell cell) (smoothGoal sigma gamma ell cell).2.1 test)
  simp only [startupLaplacianTest,startupTestPairing_add,add_apply] at transformed
  rw [startupWeightedRaw_second sigma gamma ell nonnegative ellNonnegative ellOne field rawField fieldFirst fieldSecond
      fieldSame fieldFirstSame fieldSecondSame cell vector test 0 0,
    startupWeightedRaw_second sigma gamma ell nonnegative ellNonnegative ellOne field rawField fieldFirst fieldSecond
      fieldSame fieldFirstSame fieldSecondSame cell vector test 1 1] at transformed
  have tensorTransfer (outer inner : Fin 2) := startupWeightedRaw_second sigma gamma ell nonnegative ellNonnegative ellOne
    (tensor outer inner) (rawTensor outer inner) (tensorFirst outer inner) (tensorSecond outer inner)
    (tensorSame outer inner) (tensorFirstSame outer inner) (tensorSecondSame outer inner) cell vector test outer inner
  have fluxTransfer (direction : Fin 2) := startupWeightedRaw_first sigma gamma ell nonnegative ellNonnegative ellOne
    (flux direction) (rawFlux direction) (fluxFirst direction) (fluxSame direction) (fluxFirstSame direction) cell vector test direction
  simp_rw [tensorTransfer,fluxTransfer] at transformed
  rw [← startupWeightedRaw_pairing sigma gamma ell zeroth rawZeroth zeroSame cell vector test] at transformed
  simp only [startupLaplacianTest,startupTestPairing_add,add_apply,startupPhaseEquationZeroth,startupPhaseEquationFlux,
    Fin.sum_univ_two,map_add,map_sub,map_smul,smul_eq_mul] at transformed ⊢
  linear_combination transformed

end Grad.CartesianStartup
