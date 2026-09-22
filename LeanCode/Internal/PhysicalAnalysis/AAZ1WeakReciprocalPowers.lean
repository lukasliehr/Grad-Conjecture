import AAW15ExactSmoothCoreConsumer
import AAR25OriginalSecondRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRadialJets
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace

abbrev annularRadiusInverse (lower : ℝ) (positive : 0 < lower) :=
  collarScalar 1 lower (annularInverseRadiusCurve lower positive)

def annularRadiusPower (lower : ℝ) (positive : 0 < lower) : ℕ →
    CollarL2 (ComplexEuclidean 1) lower →L[ℂ] CollarL2 (ComplexEuclidean 1) lower :=
  Nat.rec (ContinuousLinearMap.id ℂ _)
    (fun _ previous => (annularRadiusInverse lower positive).comp previous)

theorem annularRadiusPower_zero (lower : ℝ) (positive : 0 < lower) :
    annularRadiusPower lower positive 0 = ContinuousLinearMap.id ℂ _ := rfl

theorem annularRadiusPower_succ (lower : ℝ) (positive : 0 < lower) (order : ℕ) :
    annularRadiusPower lower positive (order + 1) =
      (annularRadiusInverse lower positive).comp (annularRadiusPower lower positive order) := rfl

theorem annularRadiusInverseSlope (lower : ℝ) (positive : 0 < lower)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (annularInverseRadiusSlope lower positive) field =
      -annularRadiusInverse lower positive (annularRadiusInverse lower positive field) := by
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower (annularInverseRadiusSlope lower positive) field,
    collarScalar_ae 1 lower (annularInverseRadiusCurve lower positive) (annularRadiusInverse lower positive field),
    collarScalar_ae 1 lower (annularInverseRadiusCurve lower positive) field,
    Lp.coeFn_neg (annularRadiusInverse lower positive (annularRadiusInverse lower positive field))]
    with radius slope outer inner negative
  rw [slope, negative, Pi.neg_apply, outer, inner, smul_smul, ← neg_smul]
  rfl

/-- The real reciprocal product rule is already a genuine weak graph law;
its apparent pole is outside the collar and requires no source trace. -/
theorem annularRadiusInverse_weak (lower : ℝ) (positive : 0 < lower)
    (value derivative : CollarL2 (ComplexEuclidean 1) lower)
    (weak : CompactWeakDerivative 1 lower value derivative) :
    CompactWeakDerivative 1 lower (annularRadiusInverse lower positive value)
      (annularRadiusInverse lower positive derivative -
        annularRadiusInverse lower positive (annularRadiusInverse lower positive value)) := by
  have result := compactWeakDerivative_divide_radius lower positive value derivative weak
  rw [annularRadiusInverseSlope] at result
  convert result using 1
  abel

/-- Actual distributional Leibniz law for every coefficient r^-j. -/
theorem annularRadiusPower_weak (lower : ℝ) (positive : 0 < lower)
    (order : ℕ) (value derivative : CollarL2 (ComplexEuclidean 1) lower)
    (weak : CompactWeakDerivative 1 lower value derivative) :
    CompactWeakDerivative 1 lower (annularRadiusPower lower positive order value)
      (annularRadiusPower lower positive order derivative -
        (order : ℝ) • annularRadiusPower lower positive (order + 1) value) := by
  induction order with
  | zero => simpa only [annularRadiusPower_zero, ContinuousLinearMap.id_apply, Nat.cast_zero, zero_smul, sub_zero] using weak
  | succ order previous =>
    have result := annularRadiusInverse_weak lower positive _ _ previous
    have algebra : annularRadiusInverse lower positive
        (annularRadiusPower lower positive order derivative -
          (order : ℝ) • annularRadiusPower lower positive (order + 1) value) -
        annularRadiusInverse lower positive (annularRadiusInverse lower positive (annularRadiusPower lower positive order value)) =
      annularRadiusPower lower positive (order + 1) derivative -
        ((order + 1 : ℕ) : ℝ) • annularRadiusPower lower positive (order + 1 + 1) value := by
      simp only [annularRadiusPower_succ, ContinuousLinearMap.comp_apply, map_sub,
        (annularRadiusInverse lower positive).map_smul_of_tower, Nat.cast_add, Nat.cast_one]
      module
    exact (congrArg (CompactWeakDerivative 1 lower (annularRadiusPower lower positive (order + 1) value)) algebra).mp result

theorem annularRadiusInverse_bound (lower : ℝ) (positive : 0 < lower)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    ‖annularRadiusInverse lower positive field‖ ≤ lower⁻¹ * ‖field‖ := by
  have bounded (radius : ℝ) (inside : radius ∈ Icc lower 1) :
      |annularInverseRadiusCurve lower positive radius| ≤ lower⁻¹ := by
    change |1 / max lower radius| ≤ lower⁻¹
    rw [max_eq_right inside.1, one_div, abs_of_pos (inv_pos.mpr (positive.trans_le inside.1))]
    exact inv_anti₀ positive inside.1
  rw [← scalarRadialMap_eq_collarScalar lower (annularInverseRadiusCurve lower positive) lower⁻¹ bounded field]
  exact scalarRadialMap_bound lower (annularInverseRadiusCurve lower positive) lower⁻¹ bounded field

theorem annularRadiusPower_bound (lower : ℝ) (positive : 0 < lower) (order : ℕ)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    ‖annularRadiusPower lower positive order field‖ ≤ (lower⁻¹) ^ order * ‖field‖ := by
  induction order with
  | zero => simp only [annularRadiusPower_zero, ContinuousLinearMap.id_apply, pow_zero, one_mul, le_refl]
  | succ order previous =>
    exact (annularRadiusInverse_bound lower positive _).trans
      ((mul_le_mul_of_nonneg_left previous (inv_pos.mpr positive).le).trans_eq (by rw [pow_succ]; ring))

end Grad.AnnularRadialJets
