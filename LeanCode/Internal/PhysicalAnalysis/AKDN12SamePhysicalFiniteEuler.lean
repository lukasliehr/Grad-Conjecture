import AKDN11ActualAffineEulerMaps

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness Grad.AnnularRadialSmoothness Grad.AnnularCurrentLow

/-- One finite reserve differentiates all the orders needed in a single
Leibniz expansion. It does not change the sharp full-cell Euler kernels. -/
theorem samePhysicalOperator_finiteEuler (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (row : Fin 3) (grade order : ℕ) :
    ∃ reserve : ℕ,
      ContDiffOn ℝ order (radialConjugatedAction parameters lower positive bounded.le
        (lowPhysicalRowKernel parameters length compact state row) grade reserve) (Icc lower 1) ∧
      ∀ rank ≤ order, ∀ radius : RadialPoint, radius.val ∈ Icc lower 1 →
        vectorEulerWithinIteratedDerivative (Icc lower 1) rank
          (radialConjugatedAction parameters lower positive bounded.le
            (lowPhysicalRowKernel parameters length compact state row) grade reserve) radius.val =
          conjugatedKernelAction parameters grade reserve radius
            (actualPhysicalConjugatedEulerKernel parameters length compact row state.val rank radius) := by
  obtain ⟨reserve,smooth⟩ := originalPhysicalRowKernel_finiteOrder parameters length compact state lower positive bounded row grade order
  have same : physicalRowEulerKernel parameters length compact row state.val 0 =
      lowPhysicalRowKernel parameters length compact state row := by
    funext radius
    exact physicalRowEulerKernel_zero parameters length compact row state radius
  refine ⟨reserve,smooth,?_⟩
  intro rank rankLe radius inside
  have regular : ContDiffOn ℝ rank
      (radialConjugatedAction parameters lower positive bounded.le
        (physicalRowEulerKernel parameters length compact row state.val 0) grade reserve) (Icc lower 1) := by
    rw [same]
    exact smooth.of_le (by exact_mod_cast rankLe)
  have actual := genuineConjugatedOperatorEuler parameters lower positive bounded
    (physicalRowEulerKernel parameters length compact row state.val)
    (physicalRowEulerKernel_derivative parameters length compact row state.val lower positive bounded)
    grade reserve rank regular radius inside
  rw [same] at actual
  exact actual

/-- Exact frequency relations persist under genuine Euler derivatives of
any of the SAME original Hilbert input curves. Both native and actual source
packets use this bounded observation identity. -/
theorem cellCurveEuler_shift {dimension : ℕ} (lower : ℝ) (bounded : lower < 1)
    (curve : ℕ → ℝ → CellL2 dimension) (smooth : ∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1))
    (same : ∀ grade reserve radius, radius ∈ Icc lower 1 → ∀ mode,
      curve (grade+reserve) radius mode=(annularFrequency mode.1 mode.2 : ℂ)^reserve • curve grade radius mode)
    (grade reserve rank : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    vectorEulerWithinIteratedDerivative (Icc lower 1) rank (curve (grade+reserve)) radius mode =
      (annularFrequency mode.1 mode.2 : ℂ)^reserve •
        vectorEulerWithinIteratedDerivative (Icc lower 1) rank (curve grade) radius mode := by
  let observe := (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).restrictScalars ℝ
  let shifted := (((annularFrequency mode.1 mode.2 : ℂ)^reserve) •
    lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).restrictScalars ℝ
  have highObserved := vectorEulerWithin_observation (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (curve (grade+reserve)) observe rank (contDiffOn_infty.mp (smooth _) rank) inside
  have lowObserved := vectorEulerWithin_observation (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (curve grade) shifted rank (contDiffOn_infty.mp (smooth _) rank) inside
  change _ = observe _ at highObserved
  change _ = shifted _ at lowObserved
  change observe (vectorEulerWithinIteratedDerivative (Icc lower 1) rank (curve (grade+reserve)) radius) =
    shifted (vectorEulerWithinIteratedDerivative (Icc lower 1) rank (curve grade) radius)
  rw [←highObserved,←lowObserved]
  apply vectorEulerWithin_congr (Icc lower 1) rank _ _ _ inside
  intro point member
  exact same grade reserve point member mode

def complexOperatorApply (source target : ℕ) :
    (CellL2 source →L[ℂ] CellL2 target) →L[ℝ] CellL2 source →L[ℝ] CellL2 target :=
  ((ContinuousLinearMap.apply ℝ (CellL2 target)).flip).comp
    (ContinuousLinearMap.restrictScalarsIsometry ℂ (CellL2 source) (CellL2 target) ℝ ℝ).toContinuousLinearMap

theorem complexOperatorApply_actual (source target : ℕ)
    (mapping : CellL2 source →L[ℂ] CellL2 target) (value : CellL2 source) :
    complexOperatorApply source target mapping value = mapping value := rfl

end Grad.OriginalCartesianTameEstimate
