import ASG34SectionBulkIdentity
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

def radialIntegralBasis (dimension : ℕ) (lower : ℝ) (radius : Icc lower (1 : ℝ))
    (coordinate : Fin dimension) : CollarL2 (ComplexEuclidean dimension) lower := by
  let : IsFiniteMeasure (volume.restrict (Icc lower (1 : ℝ))) := by
    rw [isFiniteMeasure_restrict]
    exact isCompact_Icc.measure_ne_top
  exact indicatorConstLp (s := Icc lower radius.val) 2 measurableSet_Icc (measure_ne_top _ _)
    (EuclideanSpace.single coordinate (1 : ℂ))

def radialIntervalIntegral (dimension : ℕ) (lower : ℝ) (radius : Icc lower (1 : ℝ)) :
    CollarL2 (ComplexEuclidean dimension) lower →L[ℝ] ComplexEuclidean dimension :=
  (∑ coordinate : Fin dimension,
    (innerSL ℂ (radialIntegralBasis dimension lower radius coordinate)).smulRight
      (EuclideanSpace.single coordinate (1 : ℂ))).restrictScalars ℝ

theorem radialIntegralBasis_inner (dimension : ℕ) (lower : ℝ) (radius : Icc lower (1 : ℝ))
    (coordinate : Fin dimension) (field : CollarL2 (ComplexEuclidean dimension) lower) :
    inner ℂ (radialIntegralBasis dimension lower radius coordinate) field =
      inner ℂ (EuclideanSpace.single coordinate (1 : ℂ)) (∫ point in lower..radius.val, field point) := by
  let : IsFiniteMeasure (volume.restrict (Icc lower (1 : ℝ))) := by
    rw [isFiniteMeasure_restrict]
    exact isCompact_Icc.measure_ne_top
  have restricted : Icc lower radius.val ⊆ Icc lower (1 : ℝ) := Icc_subset_Icc le_rfl radius.property.2
  have integrableField : Integrable field (volume.restrict (Icc lower radius.val)) :=
    (MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) (Lp.memLp field)).mono_measure
      (Measure.restrict_mono restricted le_rfl)
  rw [L2.inner_def]
  calc
    _ = ∫ point in Icc lower radius.val, inner ℂ (EuclideanSpace.single coordinate (1 : ℂ)) (field point)
        ∂volume.restrict (Icc lower 1) := by
      rw [← integral_indicator (μ := volume.restrict (Icc lower 1)) (s := Icc lower radius.val) measurableSet_Icc]
      apply integral_congr_ae
      have basisLaw : radialIntegralBasis dimension lower radius coordinate =ᵐ[volume.restrict (Icc lower 1)]
          (Icc lower radius.val).indicator (fun _ => EuclideanSpace.single coordinate (1 : ℂ)) :=
        indicatorConstLp_coeFn (hs := measurableSet_Icc) (hμs := measure_ne_top _ _)
      filter_upwards [basisLaw] with point literal
      rw [literal]
      by_cases inside : point ∈ Icc lower radius.val
      · simp only [indicator_of_mem inside]
      · simp only [indicator_of_notMem inside, inner_zero_left]
    _ = ∫ point in Icc lower radius.val, inner ℂ (EuclideanSpace.single coordinate (1 : ℂ)) (field point) := by
      rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr restricted]
    _ = inner ℂ (EuclideanSpace.single coordinate (1 : ℂ)) (∫ point in Icc lower radius.val, field point) :=
      integral_inner integrableField _
    _ = _ := by
      rw [intervalIntegral.integral_of_le radius.property.1, ← integral_Icc_eq_integral_Ioc]

theorem euclidean_sum_single (dimension : ℕ) (value : ComplexEuclidean dimension) :
    (∑ coordinate : Fin dimension, value coordinate • EuclideanSpace.single coordinate (1 : ℂ)) = value := by
  apply PiLp.ext
  intro coordinate
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp [PiLp.smul_apply, PiLp.single_apply]

/-- The continuous linear interval functional is the literal Bochner
integral of the actual L2 representative, at every point of the closed collar. -/
theorem radialIntervalIntegral_apply (dimension : ℕ) (lower : ℝ) (radius : Icc lower (1 : ℝ))
    (field : CollarL2 (ComplexEuclidean dimension) lower) :
    radialIntervalIntegral dimension lower radius field = ∫ point in lower..radius.val, field point := by
  unfold radialIntervalIntegral
  simp only [ContinuousLinearMap.coe_restrictScalars', sum_apply,
    ContinuousLinearMap.smulRight_apply]
  change (∑ coordinate : Fin dimension, inner ℂ (radialIntegralBasis dimension lower radius coordinate) field •
    EuclideanSpace.single coordinate (1 : ℂ)) = _
  simp only [radialIntegralBasis_inner, EuclideanSpace.inner_single_left, map_one, one_mul]
  exact euclidean_sum_single dimension _

end Grad.AnnularSourceGraph
