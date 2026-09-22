import SBT6LiteralAngular

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceBoundaryTrace
open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.QuotientProjection
open Grad.FlatSourceProjection Grad.NonlinearProduct Grad.NonlinearQuotientBounds
open Grad.BoundaryTrace Grad.CompatibleCompletion

def highForceTrace (parameters : PhaseParameters) (power : ℕ) :
    ZAmbient parameters (power + 2) →L[ℂ] SourceBoundary 1 :=
  (integerSourceTrace parameters (power + 1)).comp
    ((tangentialBoundaryCompleted parameters (power + 2)).comp
      (sourceCartesianCompleted parameters (power + 2)))

def highForceTraceConstant (power : ℕ) : ℝ :=
  ((3 : ℝ) ^ (power + 1) * Real.sqrt (traceCellConstant (power + 2))) *
    tangentialBoundaryConstant (power + 2)

theorem highForceTraceConstant_nonnegative (power : ℕ) : 0 ≤ highForceTraceConstant power :=
  mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (tangentialBoundaryConstant_nonnegative _)

theorem highForceTrace_bound (parameters : PhaseParameters) (power : ℕ)
    (field : ZAmbient parameters (power + 2)) :
    ‖highForceTrace parameters power field‖ ≤ highForceTraceConstant power * ‖field‖ := by
  change ‖integerSourceTrace parameters (power + 1)
    (tangentialBoundaryCompleted parameters (power + 2) (sourceCartesianCompleted parameters (power + 2) field))‖ ≤ _
  have inner := (tangentialBoundaryCompleted_bound parameters (power + 2) _).trans
    (mul_le_mul_of_nonneg_left (sourceCartesianCompleted_bound parameters (power + 2) field)
      (tangentialBoundaryConstant_nonnegative _))
  exact (integerSourceTrace_bound parameters (power + 1) _).trans
    ((mul_le_mul_of_nonneg_left inner (by positivity)).trans_eq (mul_assoc _ _ _).symm)

def forceOuterTrace (parameters : PhaseParameters) (power : ℕ) :
    ZAmbient parameters (power + 2) →L[ℂ] SourceBoundary 1 :=
  boundaryLower.comp (highForceTrace parameters power)

def rotationOuterTrace (parameters : PhaseParameters) (power : ℕ) :
    ZAmbient parameters (power + 2) →L[ℂ] SourceBoundary 1 :=
  boundaryAngular.comp (highForceTrace parameters power)

def fourthOuterTrace (parameters : PhaseParameters) (L : ℝ) (power : ℕ) :
    ZAmbient parameters (power + 2) →L[ℂ] SourceBoundary 1 :=
  ((L : ℂ)⁻¹ • integerSourceTrace parameters power).comp
    ((completedInclusion parameters (show power + 1 ≤ power + 2 by omega)).comp
      (sourceComponent parameters (power + 2) 3))

theorem forceOuterTrace_bound (parameters : PhaseParameters) (power : ℕ)
    (field : ZAmbient parameters (power + 2)) :
    ‖forceOuterTrace parameters power field‖ ≤ highForceTraceConstant power * ‖field‖ :=
  (boundaryLower_bound _).trans (highForceTrace_bound parameters power field)

theorem rotationOuterTrace_bound (parameters : PhaseParameters) (power : ℕ)
    (field : ZAmbient parameters (power + 2)) :
    ‖rotationOuterTrace parameters power field‖ ≤ highForceTraceConstant power * ‖field‖ :=
  (boundaryAngular_bound _).trans (highForceTrace_bound parameters power field)

def fourthOuterTraceConstant (L : ℝ) (power : ℕ) : ℝ :=
  L⁻¹ * ((3 : ℝ) ^ power * Real.sqrt (traceCellConstant (power + 1)))

theorem fourthOuterTrace_bound (parameters : PhaseParameters) (L : ℝ) (positive : 0 < L) (power : ℕ)
    (field : ZAmbient parameters (power + 2)) :
    ‖fourthOuterTrace parameters L power field‖ ≤ fourthOuterTraceConstant L power * ‖field‖ := by
  have inclusion := (completedInclusion parameters (show power + 1 ≤ power + 2 by omega)).le_opNorm (field 3)
  have lower := inclusion.trans
    ((mul_le_mul_of_nonneg_right (completedInclusion_norm_le_one parameters (show power + 1 ≤ power + 2 by omega))
      (norm_nonneg (field 3))).trans_eq (one_mul _))
  have full := lower.trans (zComponent_norm_le parameters (power + 2) 3 field)
  change ‖(L : ℂ)⁻¹ • integerSourceTrace parameters power
    (completedInclusion parameters (show power + 1 ≤ power + 2 by omega) (field 3))‖ ≤ _
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg positive.le]
  have trace := (integerSourceTrace_bound parameters power _).trans
    (mul_le_mul_of_nonneg_left full (by positivity))
  exact (mul_le_mul_of_nonneg_left trace (inv_nonneg.mpr positive.le)).trans_eq
    (mul_assoc _ _ _).symm

theorem highForceTrace_core (parameters : PhaseParameters) (power : ℕ)
    (field : SmoothQuotient parameters) (mode : ℤ × ℤ) :
    sourceBoundaryCoefficient parameters (power + 1)
      (highForceTrace parameters power (quotientEta parameters (power + 2) field)) mode =
        originalBoundaryCoefficient parameters (tangentialBoundaryCore parameters (cartesianSourceVector field)) mode := by
  simp only [highForceTrace, ContinuousLinearMap.comp_apply, sourceCartesianCompleted_core,
    tangentialBoundaryCompleted_core, integerSourceTrace_core, GradeCore.toCore_ofCore]

theorem forceOuterTrace_core (parameters : PhaseParameters) (power : ℕ)
    (field : SmoothQuotient parameters) (mode : ℤ × ℤ) :
    sourceBoundaryCoefficient parameters power
      (forceOuterTrace parameters power (quotientEta parameters (power + 2) field)) mode =
        originalBoundaryCoefficient parameters (tangentialBoundaryCore parameters (cartesianSourceVector field)) mode := by
  rw [forceOuterTrace, ContinuousLinearMap.comp_apply, boundaryLower_coefficient, highForceTrace_core]

theorem rotationOuterTrace_core (parameters : PhaseParameters) (power : ℕ)
    (field : SmoothQuotient parameters) (mode : ℤ × ℤ) :
    sourceBoundaryCoefficient parameters power
      (rotationOuterTrace parameters power (quotientEta parameters (power + 2) field)) mode =
        originalBoundaryCoefficient parameters (rotationCore parameters
          (tangentialBoundaryCore parameters (cartesianSourceVector field))) mode := by
  rw [rotationOuterTrace, ContinuousLinearMap.comp_apply, boundaryAngular_coefficient,
    highForceTrace_core, originalBoundaryCoefficient_rotation]

theorem fourthOuterTrace_core (parameters : PhaseParameters) (L : ℝ) (power : ℕ)
    (field : SmoothQuotient parameters) (mode : ℤ × ℤ) :
    sourceBoundaryCoefficient parameters power
      (fourthOuterTrace parameters L power (quotientEta parameters (power + 2) field)) mode =
        (L : ℂ)⁻¹ • originalBoundaryCoefficient parameters (field 3) mode := by
  change sourceBoundaryCoefficient parameters power ((L : ℂ)⁻¹ • integerSourceTrace parameters power
    (completedInclusion parameters (show power + 1 ≤ power + 2 by omega)
      (aGradeEta parameters (GradeCore.ofCoreLinear (field 3))))) mode = _
  rw [sourceBoundaryCoefficient_smul, completedInclusion_apply_eta, integerSourceTrace_core]
  rfl

end Grad.SourceBoundaryTrace
