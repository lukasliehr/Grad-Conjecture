import ASG20WeakConstantTests

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

def constantRadialCore (dimension : ℕ) (value : ComplexEuclidean dimension) : SmoothRadialCore dimension :=
  smoothRadialFunctionCore (fun _ : ℝ => value) contDiff_const

theorem constantRadialCore_slope (dimension : ℕ) (value : ComplexEuclidean dimension) :
    (constantRadialCore dimension value).val.val.2 = 0 := by
  apply ContinuousMap.ext
  intro radius
  exact deriv_const radius value

def constantRadialL2 (dimension : ℕ) (lower : ℝ) (value : ComplexEuclidean dimension) :
    CollarL2 (ComplexEuclidean dimension) lower :=
  collarContinuousL2 (ComplexEuclidean dimension) lower (ContinuousMap.const ℝ value)

theorem collarPairing_constant_field (dimension : ℕ) (lower : ℝ) (bounded : lower ≤ 1)
    (test : C(ℝ, ℝ)) (vector value : ComplexEuclidean dimension) :
    collarPairing lower test vector (constantRadialL2 dimension lower value) =
      (∫ radius in lower..1, test radius) • inner ℂ vector value := by
  unfold constantRadialL2
  calc
    _ = ∫ radius in lower..1, test radius • inner ℂ vector value := by
      convert collarPairing_core (dimension := dimension) lower bounded test vector (ContinuousMap.const ℝ value) using 1 <;> rfl
    _ = _ := intervalIntegral.integral_smul_const _ _

theorem collarPairing_one_integral (dimension : ℕ) (lower : ℝ)
    (vector : ComplexEuclidean dimension) (field : CollarL2 (ComplexEuclidean dimension) lower) :
    collarPairing lower (ContinuousMap.const ℝ 1) vector field =
      inner ℂ vector (∫ radius in Icc lower 1, field radius) := by
  let : IsFiniteMeasure (volume.restrict (Icc lower (1 : ℝ))) := by
    rw [isFiniteMeasure_restrict]
    exact isCompact_Icc.measure_ne_top
  rw [collarPairing_integral]
  simp only [ContinuousMap.const_apply, one_smul]
  exact integral_inner (MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) (Lp.memLp field)) vector

/-- AG2's zero-derivative conclusion, proved using actual primitive tests
and the accepted separation of L2 by compact smooth tests. -/
theorem weakZero_eq_constant (dimension : ℕ) (lower : ℝ) (bounded : lower < 1)
    (field : CollarL2 (ComplexEuclidean dimension) lower) (weak : CollarWeakDerivative lower field 0) :
    ∃ value : ComplexEuclidean dimension, field = constantRadialL2 dimension lower value := by
  let value : ComplexEuclidean dimension := (1 - lower)⁻¹ • (∫ radius in Icc lower 1, field radius)
  refine ⟨value, sub_eq_zero.mp ?_⟩
  apply collarPairing_separates lower
  intro test vector
  rw [map_sub, weakZero_pairing dimension lower bounded field weak,
    collarPairing_constant_field dimension lower bounded.le, collarPairing_one_integral]
  have innerScale : inner ℂ vector value =
      (1 - lower)⁻¹ • inner ℂ vector (∫ radius in Icc lower 1, field radius) :=
    ((innerSL ℂ vector).restrictScalars ℝ).map_smul _ _
  rw [innerScale, smul_smul, testAverage, div_eq_mul_inv, sub_self]

end Grad.AnnularSourceGraph
