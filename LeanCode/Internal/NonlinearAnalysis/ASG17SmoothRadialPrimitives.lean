import ASG16ActualSourceGraphConsumer
import Mathlib.Analysis.Normed.Lp.SmoothApprox

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

def smoothRadialValueL2 (dimension : ℕ) (lower : ℝ) :
    SmoothRadialCore dimension →ₗ[ℝ] CollarL2 (ComplexEuclidean dimension) lower where
  toFun core := collarContinuousL2 (ComplexEuclidean dimension) lower core.val.val.1
  map_add' _ _ := map_add _ _ _
  map_smul' _ _ := map_smul _ _ _

theorem smoothRadialValueL2_denseRange (dimension : ℕ) (lower : ℝ) :
    DenseRange (smoothRadialValueL2 dimension lower) := by
  let : IsFiniteMeasure (volume.restrict (Icc lower (1 : ℝ))) := by
    rw [isFiniteMeasure_restrict]
    exact isCompact_Icc.measure_ne_top
  have dense := Lp.dense_hasCompactSupport_contDiff (F := ComplexEuclidean dimension)
    (μ := volume.restrict (Icc lower 1)) (p := 2) (by norm_num)
  apply dense.mono
  rintro field ⟨function, representative, _supported, smooth⟩
  refine ⟨smoothRadialFunctionCore function smooth, ?_⟩
  apply Lp.ext
  filter_upwards [representative,
    (collarContinuous_memLp (ComplexEuclidean dimension) lower ⟨function, smooth.continuous⟩).coeFn_toLp]
    with radius fieldLaw coreLaw
  exact coreLaw.trans fieldLaw.symm

def anchoredSmoothPrimitive (dimension : ℕ) (lower : ℝ) (core : SmoothRadialCore dimension)
    (radius : ℝ) : ComplexEuclidean dimension := ∫ point in lower..radius, core.val.val.1 point

theorem anchoredSmoothPrimitive_derivative (dimension : ℕ) (lower : ℝ)
    (core : SmoothRadialCore dimension) (radius : ℝ) :
    HasDerivAt (anchoredSmoothPrimitive dimension lower core) (core.val.val.1 radius) radius :=
  intervalIntegral.integral_hasDerivAt_right
    (core.val.val.1.continuous.intervalIntegrable lower radius)
    core.val.val.1.continuous.stronglyMeasurable.stronglyMeasurableAtFilter core.val.val.1.continuous.continuousAt

theorem anchoredSmoothPrimitive_smooth (dimension : ℕ) (lower : ℝ)
    (core : SmoothRadialCore dimension) : ContDiff ℝ ∞ (anchoredSmoothPrimitive dimension lower core) := by
  apply contDiff_infty_iff_deriv.2
  refine ⟨fun radius => (anchoredSmoothPrimitive_derivative dimension lower core radius).differentiableAt, ?_⟩
  have derivative : deriv (anchoredSmoothPrimitive dimension lower core) = core.val.val.1 :=
    funext (fun radius => (anchoredSmoothPrimitive_derivative dimension lower core radius).deriv)
  rw [derivative]
  exact core.property

def anchoredPrimitiveCore (dimension : ℕ) (lower : ℝ) :
    SmoothRadialCore dimension →ₗ[ℝ] SmoothRadialCore dimension where
  toFun core := smoothRadialFunctionCore (anchoredSmoothPrimitive dimension lower core)
    (anchoredSmoothPrimitive_smooth dimension lower core)
  map_add' first second := by
    apply smoothRadialCore_ext
    intro radius
    exact intervalIntegral.integral_add (first.val.val.1.continuous.intervalIntegrable lower radius)
      (second.val.val.1.continuous.intervalIntegrable lower radius)
  map_smul' scalar core := by
    apply smoothRadialCore_ext
    intro radius
    exact intervalIntegral.integral_smul scalar _

theorem anchoredPrimitiveCore_value (dimension : ℕ) (lower : ℝ)
    (core : SmoothRadialCore dimension) (radius : ℝ) :
    (anchoredPrimitiveCore dimension lower core).val.val.1 radius =
      ∫ point in lower..radius, core.val.val.1 point := rfl

theorem anchoredPrimitiveCore_slope (dimension : ℕ) (lower : ℝ)
    (core : SmoothRadialCore dimension) :
    (anchoredPrimitiveCore dimension lower core).val.val.2 = core.val.val.1 :=
  ContinuousMap.ext (fun radius => (anchoredSmoothPrimitive_derivative dimension lower core radius).deriv)

theorem anchoredPrimitiveCore_lower (dimension : ℕ) (lower : ℝ)
    (core : SmoothRadialCore dimension) :
    (anchoredPrimitiveCore dimension lower core).val.val.1 lower = 0 := by
  rw [anchoredPrimitiveCore_value, intervalIntegral.integral_same]

end Grad.AnnularSourceGraph
