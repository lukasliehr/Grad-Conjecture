import AAG8SharpEnergyTrace

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularVariational

open Grad.ClosedJets Grad.AnnularSourceGraph
open Grad.GaugeCoefficients.Physical.Compensated

section Finite
variable {I C E : Type*} [AddCommGroup C] [Module ℂ C]
    [NormedAddCommGroup E] [NormedSpace ℂ E]

def finiteLpLinear (family : I → C →ₗ[ℂ] E) : (I →₀ C) →ₗ[ℂ] lp (fun _ : I => E) 2 := by
  classical
  exact Finsupp.lsum ℂ (fun index =>
    (lp.singleContinuousLinearMap ℂ (fun _ : I => E) 2 index).toLinearMap.comp (family index))

theorem finiteLpLinear_apply (family : I → C →ₗ[ℂ] E) (core : I →₀ C) (index : I) :
    finiteLpLinear family core index = family index (core index) := by
  classical
  rw [finiteLpLinear, Finsupp.lsum_apply, Finsupp.sum, lp.coeFn_sum, Finset.sum_apply]
  change (∑ other ∈ core.support,
    (lp.single 2 other (family other (core other)) : lp (fun _ : I => E) 2) index) = _
  simp only [lp.single_apply, Pi.single_apply]
  rw [Finset.sum_eq_single index]
  · simp only [ite_true]
  · intro other _ different
    exact if_neg (Ne.symm different)
  · intro missing
    rw [Finsupp.notMem_support_iff.mp missing, map_zero]
    simp
end Finite

def finiteAnnularTraceCore (lower : ℝ) (endpoint : Fin 2) :
    (HighAnnularMode →₀ complexSmoothRadialCore 1) →ₗ[ℂ] AnnularBoundary :=
  finiteLpLinear (C := complexSmoothRadialCore 1) (E := ComplexEuclidean 1) (fun mode : HighAnnularMode => (Real.sqrt (annularFrequency mode.val.1 mode.val.2) : ℂ) •
    complexCoreEndpoint 1 (radialEndpointRadius lower endpoint))

theorem finiteAnnularEnergyCore_apply (lower length : ℝ) (positive : 0 < lower)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) (mode : HighAnnularMode) :
    finiteAnnularEnergyCore lower length positive core mode =
      annularModeEnergyCore lower length positive mode.val.1 mode.val.2 (core mode) :=
by
  classical
  rw [finiteAnnularEnergyCore, Finsupp.lsum_apply, Finsupp.sum, lp.coeFn_sum, Finset.sum_apply]
  change (∑ other ∈ core.support,
    (lp.single 2 other (annularModeEnergyCore lower length positive other.val.1 other.val.2 (core other)) :
      AnnularEnergyAmbient lower) mode) = _
  simp only [lp.single_apply, Pi.single_apply]
  rw [Finset.sum_eq_single mode]
  · simp only [ite_true]
  · intro other _ different
    exact if_neg (Ne.symm different)
  · intro missing
    rw [Finsupp.notMem_support_iff.mp missing, map_zero]
    simp

theorem finiteAnnularTraceCore_apply (lower : ℝ) (endpoint : Fin 2)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) (mode : HighAnnularMode) :
    finiteAnnularTraceCore lower endpoint core mode =
      (Real.sqrt (annularFrequency mode.val.1 mode.val.2) : ℂ) •
        (core mode).val.1 (radialEndpointRadius lower endpoint) :=
by
  classical
  rw [finiteAnnularTraceCore, finiteLpLinear, Finsupp.lsum_apply, Finsupp.sum, lp.coeFn_sum, Finset.sum_apply]
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    lp.singleContinuousLinearMap_apply]
  simp only [lp.single_apply, Pi.single_apply]
  rw [Finset.sum_eq_single mode]
  · simp only [ite_true]
    rfl
  · intro other _ different
    exact if_neg (Ne.symm different)
  · intro missing
    rw [Finsupp.notMem_support_iff.mp missing]
    simp

theorem finiteAnnularTraceCore_bound (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) (endpoint : Fin 2)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    ‖finiteAnnularTraceCore lower endpoint core‖ ≤
      annularTraceConstant lower length * ‖finiteAnnularEnergyCore lower length positive core‖ := by
  have constantNonnegative : 0 ≤ annularTraceConstant lower length := Real.sqrt_nonneg _
  have pointwise (mode : HighAnnularMode) :=
    annularModeEnergyCore_endpoint_bound lower length positive bounded lengthPositive mode (core mode) endpoint
  have comparison : ‖finiteAnnularTraceCore lower endpoint core‖ ≤
      ‖(annularTraceConstant lower length : ℂ) • finiteAnnularEnergyCore lower length positive core‖ := by
    apply lp.norm_mono (by norm_num)
    intro mode
    change ‖finiteAnnularTraceCore lower endpoint core mode‖ ≤
      ‖(annularTraceConstant lower length : ℂ) • (finiteAnnularEnergyCore lower length positive core mode)‖
    rw [finiteAnnularTraceCore_apply, finiteAnnularEnergyCore_apply]
    simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg constantNonnegative] using pointwise mode
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

abbrev AnnularCoreGraph (lower length : ℝ) (positive : 0 < lower) :=
  coreGraphClosure (C := HighAnnularMode →₀ complexSmoothRadialCore 1)
    (E := AnnularEnergyAmbient lower) (finiteAnnularEnergyCore lower length positive)

def annularEnergyToCoreGraph (lower length : ℝ) (positive : 0 < lower) :
    annularEnergySpace lower length positive →L[ℂ] AnnularCoreGraph lower length positive :=
  { toLinearMap :=
      { toFun := fun field => ⟨field.val, field.property⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    cont := by
      exact continuous_subtype_val.subtype_mk _ }

theorem annularEnergyTrace_exists (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) (endpoint : Fin 2) :
    ∃ trace : annularEnergySpace lower length positive →L[ℂ] AnnularBoundary,
      (∀ core, trace (annularEnergyCoreInto lower length positive core) = finiteAnnularTraceCore lower endpoint core) ∧
      ‖trace‖ ≤ annularTraceConstant lower length := by
  have extension := coreGraph_extension (C := HighAnnularMode →₀ complexSmoothRadialCore 1)
    (E := AnnularEnergyAmbient lower) (T := AnnularBoundary)
    (finiteAnnularEnergyCore lower length positive) (finiteAnnularTraceCore lower endpoint)
    (annularTraceConstant lower length) (Real.sqrt_nonneg _)
    (finiteAnnularTraceCore_bound lower length positive bounded lengthPositive endpoint)
  rcases extension with ⟨trace, coreLaw, bound⟩
  refine ⟨trace.comp (annularEnergyToCoreGraph lower length positive), ?_, ?_⟩
  · intro core
    exact coreLaw core
  · apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro field
    have estimate := trace.le_opNorm (annularEnergyToCoreGraph lower length positive field)
    exact estimate.trans (mul_le_mul_of_nonneg_right bound (norm_nonneg _))

def annularEnergyTrace (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) (endpoint : Fin 2) :
    annularEnergySpace lower length positive →L[ℂ] AnnularBoundary :=
  (annularEnergyTrace_exists lower length positive bounded lengthPositive endpoint).choose

theorem annularEnergyTrace_core (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) (endpoint : Fin 2)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    annularEnergyTrace lower length positive bounded lengthPositive endpoint
      (annularEnergyCoreInto lower length positive core) = finiteAnnularTraceCore lower endpoint core :=
  (annularEnergyTrace_exists lower length positive bounded lengthPositive endpoint).choose_spec.1 core

/-- The literal zero inner trace carrier V in AG8. -/
def annularInnerZero (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) :
    Submodule ℂ (annularEnergySpace lower length positive) :=
  (annularEnergyTrace lower length positive bounded lengthPositive 0).ker

instance annularInnerZero_complete (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) :
    CompleteSpace (annularInnerZero lower length positive bounded lengthPositive) :=
  (annularEnergyTrace lower length positive bounded lengthPositive 0).isClosed_ker.completeSpace_coe

end Grad.AnnularVariational
