import SCD18CompletedDivision
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState

def reciprocalRadialWeight (lower : ℝ) (test : ℝ → ℝ) (radius : ℝ) : ℝ :=
  test radius / Real.sqrt (max lower radius)

theorem reciprocalRadialWeight_continuous (lower : ℝ) (positive : 0 < lower)
    (test : ℝ → ℝ) (continuousTest : Continuous test) :
    Continuous (reciprocalRadialWeight lower test) := by
  apply continuousTest.div (Real.continuous_sqrt.comp (continuous_const.max continuous_id))
  intro radius
  exact ne_of_gt (Real.sqrt_pos.2 (positive.trans_le (le_max_left _ _)))

theorem radial_test_memLp {dimension : ℕ} (lower : ℝ) (positive : 0 < lower)
    (test : ℝ → ℝ) (continuousTest : Continuous test) (vector : ComplexEuclidean dimension) :
    MemLp (fun radius => reciprocalRadialWeight lower test radius • vector)
      2 (volume.restrict (Icc lower 1)) := by
  let : IsFiniteMeasure (volume.restrict (Icc lower (1 : ℝ))) := by
    rw [isFiniteMeasure_restrict]
    exact isCompact_Icc.measure_ne_top
  have continuousField : Continuous (fun radius => reciprocalRadialWeight lower test radius • vector) :=
    (reciprocalRadialWeight_continuous lower positive test continuousTest).smul continuous_const
  obtain ⟨bound, bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn continuousField.continuousOn
  apply MemLp.of_bound continuousField.aestronglyMeasurable bound
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
  exact bounded radius inside

def radialTestLp {dimension : ℕ} (lower : ℝ) (positive : 0 < lower)
    (test : ℝ → ℝ) (continuousTest : Continuous test) (vector : ComplexEuclidean dimension) :
    RadialL2 dimension lower :=
  (radial_test_memLp lower positive test continuousTest vector).toLp _

def radialPairing {dimension : ℕ} (lower : ℝ) (positive : 0 < lower)
    (test : ℝ → ℝ) (continuousTest : Continuous test) (vector : ComplexEuclidean dimension) :
    RadialL2 dimension lower →L[ℂ] ℂ :=
  innerSL ℂ (radialTestLp lower positive test continuousTest vector)

theorem radialPairing_literal {dimension : ℕ} (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (test : ℝ → ℝ) (continuousTest : Continuous test) (vector : ComplexEuclidean dimension)
    (field : ℝ → ComplexEuclidean dimension) (continuousField : Continuous field) :
    radialPairing lower positive test continuousTest vector (radialToLp lower field continuousField) =
      ∫ radius in lower..1, test radius • inner ℂ vector (field radius) := by
  change inner ℂ (radialTestLp lower positive test continuousTest vector)
    (radialToLp lower field continuousField) = _
  rw [L2.inner_def, intervalIntegral.integral_of_le bounded, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [(radial_test_memLp lower positive test continuousTest vector).coeFn_toLp,
    radialToLp_ae lower field continuousField, ae_restrict_mem measurableSet_Icc]
    with radius testValue fieldValue inside
  change radialTestLp lower positive test continuousTest vector radius =
    reciprocalRadialWeight lower test radius • vector at testValue
  rw [testValue, fieldValue, inner_smul_left_eq_smul, inner_smul_right_eq_smul, smul_smul]
  have radiusPositive := positive.trans_le inside.1
  have cancel : reciprocalRadialWeight lower test radius * Real.sqrt radius = test radius := by
    rw [reciprocalRadialWeight, max_eq_right inside.1]
    exact div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.2 radiusPositive))
  rw [cancel]

end Grad.SourceCollarDivision
