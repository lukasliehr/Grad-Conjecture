import AEF1FixedOuterCollar

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularUniformBoundary
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularSourceGraph
open Grad.GaugeCoefficients.Physical.Compensated

/-- The finite smooth Fourier outer trace has the fixed-half-collar bound. -/
theorem finiteAnnularOuterTrace_uniform_bound (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    ‖finiteAnnularTraceCore lower 1 core‖ ≤ uniformOuterTraceConstant length *
      ‖finiteAnnularEnergyCore lower length positive core‖ := by
  have constantNonnegative := uniformOuterTraceConstant_nonnegative length
  have pointwise (mode : HighAnnularMode) :=
    annularModeEnergyCore_outer_uniform lower length positive lowerHalf lengthPositive mode (core mode)
  have comparison : ‖finiteAnnularTraceCore lower 1 core‖ ≤
      ‖(uniformOuterTraceConstant length : ℂ) • finiteAnnularEnergyCore lower length positive core‖ := by
    apply lp.norm_mono (by norm_num)
    intro mode
    change ‖finiteAnnularTraceCore lower 1 core mode‖ ≤
      ‖(uniformOuterTraceConstant length : ℂ) •
        (finiteAnnularEnergyCore lower length positive core mode)‖
    rw [finiteAnnularTraceCore_apply, finiteAnnularEnergyCore_apply]
    simpa only [show radialEndpointRadius lower (1 : Fin 2) = 1 from rfl,
      norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg constantNonnegative] using pointwise mode
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg constantNonnegative] using comparison

local instance smoothCoreGroup : AddCommGroup (complexSmoothRadialCore 1) :=
  (complexSmoothRadialCore 1).toAddSubgroup.toAddCommGroup
local instance finiteCoreGroup : AddCommGroup (HighAnnularMode →₀ complexSmoothRadialCore 1) := inferInstance
local instance energyGroup (lower length : ℝ) (positive : 0 < lower) :
    NormedAddCommGroup (annularEnergySpace lower length positive) := inferInstance
local instance energySeminormed (lower length : ℝ) (positive : 0 < lower) :
    SeminormedAddCommGroup (annularEnergySpace lower length positive) :=
  (energyGroup lower length positive).toSeminormedAddCommGroup
local instance energyNormedSpace (lower length : ℝ) (positive : 0 < lower) :
    NormedSpace ℂ (annularEnergySpace lower length positive) where
  norm_smul_le scalar field := norm_smul_le scalar field.val

/-- A bounded extension of the literal outer trace with radius-independent norm. -/
theorem uniformOuterTrace_exists (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) :
    ∃ trace : annularEnergySpace lower length positive →L[ℂ] AnnularBoundary,
      (∀ core, trace (annularEnergyCoreInto lower length positive core) =
        finiteAnnularTraceCore lower 1 core) ∧
      ‖trace‖ ≤ uniformOuterTraceConstant length := by
  have extension := coreGraph_extension (C := HighAnnularMode →₀ complexSmoothRadialCore 1)
    (E := AnnularEnergyAmbient lower) (T := AnnularBoundary)
    (finiteAnnularEnergyCore lower length positive) (finiteAnnularTraceCore lower 1)
    (uniformOuterTraceConstant length) (uniformOuterTraceConstant_nonnegative length)
    (finiteAnnularOuterTrace_uniform_bound lower length positive lowerHalf lengthPositive)
  rcases extension with ⟨trace, coreLaw, bound⟩
  refine ⟨trace.comp (annularEnergyToCoreGraph lower length positive), ?_, ?_⟩
  · intro core
    exact coreLaw core
  · apply ContinuousLinearMap.opNorm_le_bound _ (uniformOuterTraceConstant_nonnegative length)
    intro field
    exact (trace.le_opNorm (annularEnergyToCoreGraph lower length positive field)).trans
      (mul_le_mul_of_nonneg_right bound (norm_nonneg _))

def uniformOuterTrace (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) :
    annularEnergySpace lower length positive →L[ℂ] AnnularBoundary :=
  (uniformOuterTrace_exists lower length positive lowerHalf lengthPositive).choose

@[simp] theorem uniformOuterTrace_core (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    uniformOuterTrace lower length positive lowerHalf lengthPositive
      (annularEnergyCoreInto lower length positive core) =
    finiteAnnularTraceCore lower 1 core :=
  (uniformOuterTrace_exists lower length positive lowerHalf lengthPositive).choose_spec.1 core

/-- The uniform extension is the already accepted physical AAG outer trace,
because both continuous maps agree on the actual dense smooth core. -/
theorem uniformOuterTrace_eq_annularEnergyTrace (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (collar : lower < 1) (lengthPositive : 0 < length) :
    uniformOuterTrace lower length positive lowerHalf lengthPositive =
      annularEnergyTrace lower length positive collar lengthPositive 1 := by
  apply ContinuousLinearMap.ext
  intro field
  apply isClosed_property (annularEnergyCoreInto_denseRange lower length positive)
    (isClosed_eq (uniformOuterTrace lower length positive lowerHalf lengthPositive).continuous
      (annularEnergyTrace lower length positive collar lengthPositive 1).continuous) _ field
  intro core
  rw [uniformOuterTrace_core, annularEnergyTrace_core]

/-- Uniform outer endpoint bound for the literal accepted AAG trace. -/
theorem annularEnergyOuterTrace_uniform_bound (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (collar : lower < 1) (lengthPositive : 0 < length)
    (field : annularEnergySpace lower length positive) :
    ‖annularEnergyTrace lower length positive collar lengthPositive 1 field‖ ≤
      uniformOuterTraceConstant length * ‖field‖ := by
  rw [← uniformOuterTrace_eq_annularEnergyTrace lower length positive lowerHalf collar lengthPositive]
  exact ((uniformOuterTrace lower length positive lowerHalf lengthPositive).le_opNorm field).trans
    (mul_le_mul_of_nonneg_right
      (uniformOuterTrace_exists lower length positive lowerHalf lengthPositive).choose_spec.2
      (norm_nonneg field))

end Grad.AnnularUniformBoundary
