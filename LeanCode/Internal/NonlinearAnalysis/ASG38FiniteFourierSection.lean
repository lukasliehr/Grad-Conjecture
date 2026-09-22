import ASG37ActualWeakRadialRepresentative

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

abbrev FourierContinuousSection (dimension : ℕ) (lower : ℝ) :=
  C(Icc lower (1 : ℝ), lp (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2)

def smoothFourierSingleSection (dimension : ℕ) (lower : ℝ) (mode : ℤ × ℤ) :
    SmoothRadialCore dimension →ₗ[ℝ] FourierContinuousSection dimension lower where
  toFun core := ⟨fun radius => lp.single 2 mode (core.val.val.1 radius.val),
    (lp.singleContinuousLinearMap ℝ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).continuous.comp
      (core.val.val.1.continuous.comp continuous_subtype_val)⟩
  map_add' first second := by
    apply ContinuousMap.ext
    intro radius
    exact map_add (lp.singleContinuousLinearMap ℝ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode)
      (first.val.val.1 radius.val) (second.val.val.1 radius.val)
  map_smul' scalar core := by
    apply ContinuousMap.ext
    intro radius
    exact map_smul (lp.singleContinuousLinearMap ℝ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode)
      scalar (core.val.val.1 radius.val)

def finiteFourierSection (dimension : ℕ) (lower : ℝ) :
    ((ℤ × ℤ) →₀ SmoothRadialCore dimension) →ₗ[ℝ] FourierContinuousSection dimension lower :=
  Finsupp.lsum ℝ (smoothFourierSingleSection dimension lower)

theorem finiteFourierSection_apply (dimension : ℕ) (lower : ℝ)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    finiteFourierSection dimension lower core radius mode = (core mode).val.val.1 radius.val := by
  classical
  rw [finiteFourierSection, Finsupp.lsum_apply, Finsupp.sum]
  simp only [ContinuousMap.sum_apply, lp.coeFn_sum, Finset.sum_apply]
  change (∑ other ∈ core.support,
    (lp.single 2 other ((core other).val.val.1 radius.val) :
      lp (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2) mode) = _
  simp only [lp.single_apply, Pi.single_apply]
  rw [Finset.sum_eq_single mode]
  · simp only [ite_true]
  · intro other _ different
    exact if_neg (Ne.symm different)
  · intro missing
    rw [Finsupp.notMem_support_iff.mp missing]
    simp

theorem finiteFourierSection_bound (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) :
    ‖finiteFourierSection dimension lower core‖ ≤
      sourceEndpointConstant lower * ‖finiteSourceCore parameters dimension lower angular cell core‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).2
  intro radius
  calc
    _ ≤ ‖sourceEndpointConstant lower • finiteSourceCore parameters dimension lower angular cell core‖ := by
      apply lp.norm_mono (by norm_num)
      intro mode
      rw [finiteFourierSection_apply]
      change ‖(core mode).val.val.1 radius.val‖ ≤
        ‖sourceEndpointConstant lower • (finiteSourceCore parameters dimension lower angular cell core mode)‖
      rw [finiteSourceCore_apply, norm_smul, Real.norm_of_nonneg (show 0 ≤ sourceEndpointConstant lower from Real.sqrt_nonneg _)]
      exact smoothRadial_point_bound dimension lower positive bounded (core mode) radius
    _ = _ := by
      rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ sourceEndpointConstant lower from Real.sqrt_nonneg _)]
      rfl

end Grad.AnnularSourceGraph
