import ASG1WeightedRadialCompletion
import BKA2ShiftWeights

noncomputable section

set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryKernelAction Grad.PhaseAlgebra

theorem smoothRadialCore_ext {dimension : ℕ} {first second : SmoothRadialCore dimension}
    (same : ∀ radius, first.val.val.1 radius = second.val.val.1 radius) : first = second := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact ContinuousMap.ext same
  · apply ContinuousMap.ext
    intro radius
    have functions : (first.val.val.1 : ℝ → ComplexEuclidean dimension) = second.val.val.1 := funext same
    have firstDerivative := first.val.property radius
    rw [functions] at firstDerivative
    exact firstDerivative.unique (second.val.property radius)

def smoothRadialFunctionCore {dimension : ℕ} (function : ℝ → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ function) : SmoothRadialCore dimension :=
  ⟨⟨(⟨function, smooth.continuous⟩,
       ⟨deriv function, (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩),
      fun radius => (smooth.differentiable (by simp) radius).hasDerivAt⟩, smooth⟩

theorem smoothRadialFunctionCore_value {dimension : ℕ} (function : ℝ → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ function) (radius : ℝ) :
    (smoothRadialFunctionCore function smooth).val.val.1 radius = function radius := rfl

def smoothRadialScalarMap (dimension : ℕ) (coefficient : ℝ → ℝ)
    (coefficientSmooth : ContDiff ℝ ∞ coefficient) : SmoothRadialCore dimension →ₗ[ℝ] SmoothRadialCore dimension where
  toFun core := smoothRadialFunctionCore (fun radius => coefficient radius • core.val.val.1 radius)
    (coefficientSmooth.smul (show ContDiff ℝ ∞ core.val.val.1 from core.property))
  map_add' first second := by
    apply smoothRadialCore_ext
    intro radius
    exact smul_add _ _ _
  map_smul' scalar core := by
    apply smoothRadialCore_ext
    intro radius
    exact smul_comm (coefficient radius) scalar (core.val.val.1 radius)

theorem smoothRadialScalarMap_value (dimension : ℕ) (coefficient : ℝ → ℝ)
    (coefficientSmooth : ContDiff ℝ ∞ coefficient) (core : SmoothRadialCore dimension) (radius : ℝ) :
    (smoothRadialScalarMap dimension coefficient coefficientSmooth core).val.val.1 radius =
      coefficient radius • core.val.val.1 radius := rfl

/-- The literal AH10 normalization, including the original curved analytic
phase rather than its equivalent linear envelope. -/
def annularConjugatingWeight (parameters : PhaseParameters) (angular cell : ℕ)
    (mode : ℤ × ℤ) (radius : ℝ) : ℝ :=
  splitTangentialWeight angular cell mode * Real.exp (radialPhase parameters radius mode.2)

theorem annularConjugatingWeight_pos (parameters : PhaseParameters) (angular cell : ℕ)
    (mode : ℤ × ℤ) (radius : ℝ) : 0 < annularConjugatingWeight parameters angular cell mode radius :=
  mul_pos (splitTangentialWeight_pos angular cell mode) (Real.exp_pos _)

theorem radialPhase_smooth (parameters : PhaseParameters) (cell : ℤ) :
    ContDiff ℝ ∞ (fun radius => radialPhase parameters radius cell) := by
  have polynomial : ContDiff ℝ ∞ (fun radius : ℝ => 1 + cellFrequency cell ^ 2 * radius ^ 2) := by fun_prop
  have root := polynomial.sqrt (fun radius => by positivity : ∀ radius : ℝ, 1 + cellFrequency cell ^ 2 * radius ^ 2 ≠ 0)
  exact contDiff_const.sub (contDiff_const.mul (root.sub contDiff_const))

theorem annularConjugatingWeight_smooth (parameters : PhaseParameters) (angular cell : ℕ)
    (mode : ℤ × ℤ) : ContDiff ℝ ∞ (annularConjugatingWeight parameters angular cell mode) :=
  contDiff_const.mul (radialPhase_smooth parameters mode.2).exp

def annularNormalizeCore (parameters : PhaseParameters) (dimension angular cell : ℕ)
    (mode : ℤ × ℤ) : SmoothRadialCore dimension →ₗ[ℝ] SmoothRadialCore dimension :=
  smoothRadialScalarMap dimension (annularConjugatingWeight parameters angular cell mode)
    (annularConjugatingWeight_smooth parameters angular cell mode)

def annularDenormalizeCore (parameters : PhaseParameters) (dimension angular cell : ℕ)
    (mode : ℤ × ℤ) : SmoothRadialCore dimension →ₗ[ℝ] SmoothRadialCore dimension :=
  smoothRadialScalarMap dimension (fun radius => (annularConjugatingWeight parameters angular cell mode radius)⁻¹)
    ((annularConjugatingWeight_smooth parameters angular cell mode).inv
      (fun radius => (annularConjugatingWeight_pos parameters angular cell mode radius).ne'))

theorem annularNormalizeCore_left (parameters : PhaseParameters) (dimension angular cell : ℕ)
    (mode : ℤ × ℤ) (core : SmoothRadialCore dimension) :
    annularDenormalizeCore parameters dimension angular cell mode
      (annularNormalizeCore parameters dimension angular cell mode core) = core := by
  apply smoothRadialCore_ext
  intro radius
  change (annularConjugatingWeight parameters angular cell mode radius)⁻¹ •
    (annularConjugatingWeight parameters angular cell mode radius • core.val.val.1 radius) = _
  rw [smul_smul, inv_mul_cancel₀ (annularConjugatingWeight_pos parameters angular cell mode radius).ne', one_smul]

theorem annularNormalizeCore_right (parameters : PhaseParameters) (dimension angular cell : ℕ)
    (mode : ℤ × ℤ) (core : SmoothRadialCore dimension) :
    annularNormalizeCore parameters dimension angular cell mode
      (annularDenormalizeCore parameters dimension angular cell mode core) = core := by
  apply smoothRadialCore_ext
  intro radius
  change annularConjugatingWeight parameters angular cell mode radius •
    ((annularConjugatingWeight parameters angular cell mode radius)⁻¹ • core.val.val.1 radius) = _
  rw [smul_smul, mul_inv_cancel₀ (annularConjugatingWeight_pos parameters angular cell mode radius).ne', one_smul]

def phaseConjugatedCurve (parameters : PhaseParameters) (mode : ℤ × ℤ)
    {dimension : ℕ} (core : SmoothRadialCore dimension) (radius : ℝ) : ComplexEuclidean dimension :=
  Real.exp (radialPhase parameters radius mode.2) • core.val.val.1 radius

theorem phaseConjugatedCurve_smooth (parameters : PhaseParameters) (mode : ℤ × ℤ)
    {dimension : ℕ} (core : SmoothRadialCore dimension) : ContDiff ℝ ∞ (phaseConjugatedCurve parameters mode core) :=
  (radialPhase_smooth parameters mode.2).exp.smul
    (show ContDiff ℝ ∞ core.val.val.1 from core.property)

theorem annularNormalizeCore_value (parameters : PhaseParameters) (dimension angular cell : ℕ)
    (mode : ℤ × ℤ) (core : SmoothRadialCore dimension) (radius : ℝ) :
    (annularNormalizeCore parameters dimension angular cell mode core).val.val.1 radius =
      splitTangentialWeight angular cell mode • phaseConjugatedCurve parameters mode core radius :=
  mul_smul _ _ _

theorem annularNormalizeCore_slope (parameters : PhaseParameters) (dimension angular cell : ℕ)
    (mode : ℤ × ℤ) (core : SmoothRadialCore dimension) (radius : ℝ) :
    (annularNormalizeCore parameters dimension angular cell mode core).val.val.2 radius =
      splitTangentialWeight angular cell mode • deriv (phaseConjugatedCurve parameters mode core) radius := by
  have derivative := ((phaseConjugatedCurve_smooth parameters mode core).differentiable (by simp) radius).hasDerivAt.const_smul
    (splitTangentialWeight angular cell mode)
  have stored := (annularNormalizeCore parameters dimension angular cell mode core).val.property radius
  have functions :
      ((annularNormalizeCore parameters dimension angular cell mode core).val.val.1 : ℝ → ComplexEuclidean dimension) =
      fun point => splitTangentialWeight angular cell mode • phaseConjugatedCurve parameters mode core point :=
    funext (annularNormalizeCore_value parameters dimension angular cell mode core)
  rw [functions] at stored
  exact stored.unique derivative

end Grad.AnnularSourceGraph
