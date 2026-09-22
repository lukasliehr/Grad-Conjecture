import AEK8CompleteKnownDataFunctional

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularCurrentSource

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.AnnularSourceGraph
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The terminal source trace constant evaluated on the fixed half collar. -/
def uniformSourceOuterConstant : ℝ := sourceEndpointConstant (1 / 2)

theorem uniformSourceOuterConstant_nonnegative : 0 ≤ uniformSourceOuterConstant :=
  Real.sqrt_nonneg _

/-- Restriction of the genuine weighted radial graph energy to `[1/2,1]`
can only lower its norm. -/
theorem halfWeightedRadialCore_norm_le (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (core : SmoothRadialCore dimension) :
    ‖weightedRadialCoreInto dimension (1 / 2) core‖ ≤
      ‖weightedRadialCoreInto dimension lower core‖ := by
  let integrand : ℝ → ℝ := fun radius => radius *
    (‖core.val.val.1 radius‖ ^ 2 + ‖core.val.val.2 radius‖ ^ 2)
  have lowerOne : lower ≤ 1 := lowerHalf.trans (by norm_num)
  have integrable : IntervalIntegrable integrand volume lower 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_id.mul
      ((core.val.val.1.continuous.norm.pow 2).add
        (core.val.val.2.continuous.norm.pow 2))
  have nonnegative : ∀ radius ∈ Icc lower 1, 0 ≤ integrand radius := by
    intro radius inside
    exact mul_nonneg (positive.le.trans inside.1)
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have restricted : (∫ radius in (1 / 2 : ℝ)..1, integrand radius) ≤
      ∫ radius in lower..1, integrand radius := by
    apply intervalIntegral.integral_mono_interval lowerHalf (by norm_num) le_rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
      exact nonnegative radius ⟨inside.1.le, inside.2⟩
    · exact integrable
  have halfSq := weightedRadialCore_norm_sq dimension (1 / 2) (by norm_num)
    (by norm_num) core
  have fullSq := weightedRadialCore_norm_sq dimension lower positive lowerOne core
  change ‖weightedRadialCoreInto dimension (1 / 2) core‖ ^ 2 =
    ∫ radius in (1 / 2 : ℝ)..1, integrand radius at halfSq
  change ‖weightedRadialCoreInto dimension lower core‖ ^ 2 =
    ∫ radius in lower..1, integrand radius at fullSq
  nlinarith [norm_nonneg (weightedRadialCoreInto dimension (1 / 2) core),
    norm_nonneg (weightedRadialCoreInto dimension lower core)]

/-- Fixed-half-collar terminal evaluation on every genuine smooth radial
source graph. -/
theorem smoothRadialOuter_uniform_bound (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (core : SmoothRadialCore dimension) :
    ‖smoothRadialEndpoint dimension lower 1 core‖ ≤
      uniformSourceOuterConstant * ‖weightedRadialCoreInto dimension lower core‖ := by
  have fixed := smoothRadialEndpoint_bound dimension (1 / 2) (by norm_num)
    (by norm_num) 1 core
  have restricted := halfWeightedRadialCore_norm_le dimension lower positive lowerHalf core
  change ‖core.val.val.1 1‖ ≤ _
  change ‖core.val.val.1 1‖ ≤
    sourceEndpointConstant (1 / 2) *
      ‖weightedRadialCoreInto dimension (1 / 2) core‖ at fixed
  exact fixed.trans (mul_le_mul_of_nonneg_left restricted
    uniformSourceOuterConstant_nonnegative)

/-- A continuous terminal evaluation constructed with the fixed-half-collar
constant on the original completed weighted radial graph. -/
theorem uniformWeightedRadialOuterTrace_exists (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) :
    ∃ trace : WeightedRadialH1 dimension lower →L[ℝ] ComplexEuclidean dimension,
      (∀ core, trace (weightedRadialCoreInto dimension lower core) =
        core.val.val.1 1) ∧
      (∀ field, ‖trace field‖ ≤ uniformSourceOuterConstant * ‖field‖) := by
  have extension : ∃ trace :
      (LinearMap.range (weightedRadialCore dimension lower)).topologicalClosure →L[ℝ]
        ComplexEuclidean dimension,
      (∀ core, trace ⟨weightedRadialCore dimension lower core,
        Submodule.le_topologicalClosure _ ⟨core, rfl⟩⟩ =
          smoothRadialEndpoint dimension lower 1 core) ∧
      (∀ field, ‖trace field‖ ≤ uniformSourceOuterConstant * ‖field‖) := by
    with_reducible exact (collarRange_extension
      (C := SmoothRadialCore dimension) (F := WeightedRadialAmbient dimension lower)
      (T := ComplexEuclidean dimension) (weightedRadialCore dimension lower)
      (smoothRadialEndpoint dimension lower 1) uniformSourceOuterConstant
      uniformSourceOuterConstant_nonnegative
      (smoothRadialOuter_uniform_bound dimension lower positive lowerHalf))
  obtain ⟨trace, coreLaw, bound⟩ := extension
  refine ⟨trace, ?_, bound⟩
  intro core
  exact coreLaw core

def uniformWeightedRadialOuterTrace (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) :
    WeightedRadialH1 dimension lower →L[ℝ] ComplexEuclidean dimension :=
  (uniformWeightedRadialOuterTrace_exists dimension lower positive lowerHalf).choose

@[simp] theorem uniformWeightedRadialOuterTrace_core (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (core : SmoothRadialCore dimension) :
    uniformWeightedRadialOuterTrace dimension lower positive lowerHalf
      (weightedRadialCoreInto dimension lower core) = core.val.val.1 1 :=
  (uniformWeightedRadialOuterTrace_exists dimension lower positive lowerHalf).choose_spec.1 core

theorem uniformWeightedRadialOuterTrace_bound (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (field : WeightedRadialH1 dimension lower) :
    ‖uniformWeightedRadialOuterTrace dimension lower positive lowerHalf field‖ ≤
      uniformSourceOuterConstant * ‖field‖ :=
  (uniformWeightedRadialOuterTrace_exists dimension lower positive lowerHalf).choose_spec.2 field

/-- The new fixed-collar extension is the already accepted genuine terminal
trace, by density of the same smooth radial graph. -/
theorem uniformWeightedRadialOuterTrace_eq (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) :
    uniformWeightedRadialOuterTrace dimension lower positive lowerHalf =
      weightedRadialTrace dimension lower positive
        (lowerHalf.trans_lt (by norm_num)) 1 := by
  apply weightedRadialTrace_unique dimension lower positive
    (lowerHalf.trans_lt (by norm_num)) 1
  intro core
  rw [uniformWeightedRadialOuterTrace_core]
  rfl

/-- Uniform terminal trace bound for the literal accepted source graph. -/
theorem weightedRadialTrace_outer_uniform_bound (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (field : WeightedRadialH1 dimension lower) :
    ‖weightedRadialTrace dimension lower positive
      (lowerHalf.trans_lt (by norm_num)) 1 field‖ ≤
      uniformSourceOuterConstant * ‖field‖ := by
  rw [← uniformWeightedRadialOuterTrace_eq dimension lower positive lowerHalf]
  exact uniformWeightedRadialOuterTrace_bound dimension lower positive lowerHalf field

/-- The same fixed-collar estimate after summing all Fourier modes of a
completed annular source graph. -/
theorem annularSourceTrace_outer_uniform_bound (parameters : PhaseParameters)
    (dimension : ℕ) (lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (angular cell : ℕ)
    (field : AnnularSourceH1 parameters dimension lower angular cell) :
    ‖annularSourceTrace parameters dimension lower positive
      (lowerHalf.trans_lt (by norm_num)) angular cell 1 field‖ ≤
      uniformSourceOuterConstant * ‖field‖ := by
  let uniformMap := lpTwoMap
    (fun _ : ℤ × ℤ => uniformWeightedRadialOuterTrace dimension lower positive lowerHalf)
    uniformSourceOuterConstant uniformSourceOuterConstant_nonnegative
    (fun _ => uniformWeightedRadialOuterTrace_bound dimension lower positive lowerHalf)
  have same : annularSourceTrace parameters dimension lower positive
      (lowerHalf.trans_lt (by norm_num)) angular cell 1 field = uniformMap field := by
    apply lp.ext
    funext mode
    change weightedRadialTrace dimension lower positive
      (lowerHalf.trans_lt (by norm_num)) 1 (field mode) =
      uniformWeightedRadialOuterTrace dimension lower positive lowerHalf (field mode)
    rw [uniformWeightedRadialOuterTrace_eq]
  rw [same]
  exact lpTwoMap_bound _ _ _ _ field

end Grad.AnnularCurrentSource
