import BL18FiniteEnergy

noncomputable section

open Set Filter
open scoped BigOperators ContDiff Topology

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

theorem collarPlane_eq_scaled_boundary (time angle : ℝ) :
    collarPlane (time, angle) = (1 - time) • boundaryCirclePoint (angle : CellCircle) := by
  rw [boundaryCirclePoint_coe]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [collarPlane]

theorem cartesianWeight_collar (parameters : PhaseParameters) (cell : ℤ) (time angle : ℝ) :
    cartesianWeight parameters cell (collarPlane (time, angle)) = radialWeight parameters cell time := by
  rw [radialWeight, cartesianWeight_exp, cartesianWeight_exp, cartesianPhase_formula,
    cartesianPhase_formula, collarPlane_norm, radialLine_norm]

theorem weightedKernel_polar (parameters : PhaseParameters) (mode : ℤ × ℤ) (time angle : ℝ)
    (beforeAxis : time < 1) :
    (cartesianWeight parameters mode.2 (collarPlane (time, angle)) : ℂ) *
        boundaryKernel mode (collarPlane (time, angle)) =
      (conjugatedProfile parameters mode time : ℂ) * cellExponential mode.1 angle *
        (Real.exp (boundaryPhase parameters mode.2) : ℂ) := by
  rw [cartesianWeight_collar, collarPlane_eq_scaled_boundary, boundaryKernel_polar mode time beforeAxis,
    ← cellCharacter_coe]
  change (radialWeight parameters mode.2 time : ℂ) *
      ((collarCutoff1D time : ℂ) * (Real.exp (-boundaryFrequency mode * time) : ℂ) * cellCharacter mode.1 angle) = _
  rw [conjugatedProfile, conjugatedExponentialProfile_weight]
  have exponentialNonzero : (Real.exp (boundaryPhase parameters mode.2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  simp only [Complex.ofReal_mul, Complex.ofReal_div, radialWeight, cellCharacter_coe]
  field_simp

def finiteKernelField {dimension : ℕ} (cell : ℤ) (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean dimension) (point : SpatialPlane) : ComplexEuclidean dimension :=
  ∑ mode ∈ modes, boundaryKernel (mode, cell) point • values mode

theorem finiteKernelField_smooth {dimension : ℕ} (cell : ℤ) (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean dimension) : ContDiff ℝ ∞ (finiteKernelField cell modes values) := by
  apply ContDiff.sum
  intro mode _
  exact (boundaryKernel_smooth (mode, cell)).smul contDiff_const

def weightedFiniteKernelField {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ) (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean dimension) (point : SpatialPlane) : ComplexEuclidean dimension :=
  (cartesianWeight parameters cell point : ℂ) • finiteKernelField cell modes values point

theorem weightedFiniteKernelField_smooth {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension) :
    ContDiff ℝ ∞ (weightedFiniteKernelField parameters cell modes values) :=
  (Complex.ofRealCLM.contDiff.comp (cartesianWeight_contDiff parameters cell)).smul
    (finiteKernelField_smooth cell modes values)

theorem weightedFiniteKernelField_polar {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension) (point : ℝ × ℝ)
    (beforeAxis : point.1 < 1) :
    weightedFiniteKernelField parameters cell modes values (collarPlane point) =
      finitePolarField parameters cell modes (fun mode => (Real.exp (boundaryPhase parameters cell) : ℂ) • values mode) point := by
  rw [weightedFiniteKernelField, finiteKernelField, Finset.smul_sum]
  simp only [finitePolarField, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro mode _
  rw [smul_smul, weightedKernel_polar parameters (mode, cell) point.1 point.2 beforeAxis]
  apply PiLp.ext
  intro coordinate
  simp only [polarModeField, PiLp.smul_apply, Complex.real_smul, smul_eq_mul]
  ring

theorem weightedFiniteKernelField_polar_derivative {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension) (order : ℕ) (point : ℝ × ℝ)
    (beforeAxis : point.1 < 1) :
    iteratedFDeriv ℝ order (weightedFiniteKernelField parameters cell modes values ∘ collarPlane) point =
      iteratedFDeriv ℝ order (finitePolarField parameters cell modes
        (fun mode => (Real.exp (boundaryPhase parameters cell) : ℂ) • values mode)) point := by
  have openRegion : IsOpen {source : ℝ × ℝ | source.1 < 1} := isOpen_lt continuous_fst continuous_const
  have agreement : (weightedFiniteKernelField parameters cell modes values ∘ collarPlane) =ᶠ[𝓝 point]
      finitePolarField parameters cell modes (fun mode => (Real.exp (boundaryPhase parameters cell) : ℂ) • values mode) := by
    filter_upwards [openRegion.mem_nhds beforeAxis] with source sourceIn
    exact weightedFiniteKernelField_polar parameters cell modes values source sourceIn
  exact (agreement.iteratedFDeriv (𝕜 := ℝ) order).eq_of_nhds

def finiteBoundaryJet {dimension : ℕ} (cell : ℤ) (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean dimension) : ClosedJet dimension :=
  globalClosedJet (finiteKernelField cell modes values) (finiteKernelField_smooth cell modes values)

theorem finiteBoundaryJet_weighted {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension) :
    phaseWeightedJet parameters cell (finiteBoundaryJet cell modes values) =
      globalClosedJet (weightedFiniteKernelField parameters cell modes values)
        (weightedFiniteKernelField_smooth parameters cell modes values) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rfl

end Grad.BoundaryLift
