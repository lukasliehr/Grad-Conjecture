import ASG6FourierCompletion

noncomputable section

set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

section Lift

variable {Index E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

def lpTwoMapLinear (family : Index → E →L[ℝ] F) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index value, ‖family index value‖ ≤ constant * ‖value‖) :
    lp (fun _ : Index => E) 2 →ₗ[ℝ] lp (fun _ : Index => F) 2 where
  toFun field := ⟨fun index => family index (field index),
    (lp.memℓp (constant • field)).mono' (fun index => by
      change ‖family index (field index)‖ ≤ ‖constant • field index‖
      rw [norm_smul, Real.norm_of_nonneg nonnegative]
      exact bounded index (field index))⟩
  map_add' first second := by
    apply Subtype.ext
    funext index
    exact map_add (family index) (first index) (second index)
  map_smul' scalar field := by
    apply Subtype.ext
    funext index
    exact map_smul (family index) scalar (field index)

theorem lpTwoMapLinear_bound (family : Index → E →L[ℝ] F) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index value, ‖family index value‖ ≤ constant * ‖value‖)
    (field : lp (fun _ : Index => E) 2) :
    ‖lpTwoMapLinear family constant nonnegative bounded field‖ ≤ constant * ‖field‖ := by
  calc
    _ ≤ ‖constant • field‖ := by
      apply lp.norm_mono (by norm_num)
      intro index
      change ‖family index (field index)‖ ≤ ‖constant • field index‖
      rw [norm_smul, Real.norm_of_nonneg nonnegative]
      exact bounded index (field index)
    _ = _ := by rw [norm_smul, Real.norm_of_nonneg nonnegative]

def lpTwoMap (family : Index → E →L[ℝ] F) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index value, ‖family index value‖ ≤ constant * ‖value‖) :
    lp (fun _ : Index => E) 2 →L[ℝ] lp (fun _ : Index => F) 2 :=
  (lpTwoMapLinear family constant nonnegative bounded).mkContinuous constant
    (lpTwoMapLinear_bound family constant nonnegative bounded)

theorem lpTwoMap_apply (family : Index → E →L[ℝ] F) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index value, ‖family index value‖ ≤ constant * ‖value‖)
    (field : lp (fun _ : Index => E) 2) (index : Index) :
    lpTwoMap family constant nonnegative bounded field index = family index (field index) := rfl

theorem lpTwoMap_bound (family : Index → E →L[ℝ] F) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index value, ‖family index value‖ ≤ constant * ‖value‖)
    (field : lp (fun _ : Index => E) 2) :
    ‖lpTwoMap family constant nonnegative bounded field‖ ≤ constant * ‖field‖ :=
  lpTwoMapLinear_bound family constant nonnegative bounded field

end Lift

abbrev AnnularEndpointTrace (_parameters : PhaseParameters) (dimension : ℕ)
    (_radius : ℝ) (_angular _cell : ℕ) := lp (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2

/-- AH11 at either endpoint on the entire complete two-frequency graph. -/
def annularSourceTrace (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ) (endpoint : Fin 2) :
    AnnularSourceH1 parameters dimension lower angular cell →L[ℝ]
      AnnularEndpointTrace parameters dimension (radialEndpointRadius lower endpoint) angular cell :=
  lpTwoMap (fun _ => weightedRadialTrace dimension lower positive bounded endpoint)
    (sourceEndpointConstant lower) (Real.sqrt_nonneg _)
    (fun _ => weightedRadialTrace_bound dimension lower positive bounded endpoint)

theorem annularSourceTrace_apply (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ) (endpoint : Fin 2)
    (field : AnnularSourceH1 parameters dimension lower angular cell) (mode : ℤ × ℤ) :
    annularSourceTrace parameters dimension lower positive bounded angular cell endpoint field mode =
      weightedRadialTrace dimension lower positive bounded endpoint (field mode) := rfl

theorem annularSourceTrace_bound (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ) (endpoint : Fin 2)
    (field : AnnularSourceH1 parameters dimension lower angular cell) :
    ‖annularSourceTrace parameters dimension lower positive bounded angular cell endpoint field‖ ≤
      sourceEndpointConstant lower * ‖field‖ :=
  lpTwoMap_bound _ _ _ _ field

theorem annularSourceTrace_core (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ) (endpoint : Fin 2)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) (mode : ℤ × ℤ) :
    annularSourceTrace parameters dimension lower positive bounded angular cell endpoint
      (finiteSourceCore parameters dimension lower angular cell core) mode =
      (core mode).val.val.1 (radialEndpointRadius lower endpoint) := by
  rw [annularSourceTrace_apply, finiteSourceCore_apply, weightedRadialTrace_core]

end Grad.AnnularSourceGraph
