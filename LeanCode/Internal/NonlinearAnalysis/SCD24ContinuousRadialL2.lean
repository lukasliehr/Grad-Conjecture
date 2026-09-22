import SCD23ContinuousPolarRestriction

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace

theorem radialToLp_uniform_bound {dimension : ℕ} (lower : ℝ) (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1)
    (field : ℝ → ComplexEuclidean dimension) (continuousField : Continuous field)
    (constant : ℝ) (constantNonnegative : 0 ≤ constant)
    (bound : ∀ radius ∈ Icc lower 1, ‖field radius‖ ≤ constant) :
    ‖radialToLp lower field continuousField‖ ≤ constant := by
  have squared : ‖radialToLp lower field continuousField‖ ^ 2 ≤ constant ^ 2 := by
    rw [radialToLp_norm_sq lower nonnegative bounded]
    have integralBound := intervalIntegral.integral_mono_on
      (μ := volume) (f := fun radius => radius * ‖field radius‖ ^ 2)
      (g := fun _ => constant ^ 2) bounded
      ((continuous_id.mul (continuousField.norm.pow 2)).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) (fun radius inside => by
        exact (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (bound radius inside) 2)
          (nonnegative.trans inside.1)).trans
            ((mul_le_mul_of_nonneg_right inside.2 (sq_nonneg constant)).trans_eq (one_mul _)))
    rw [intervalIntegral.integral_const] at integralBound
    simp only [smul_eq_mul] at integralBound
    exact integralBound.trans (by nlinarith [sq_nonneg constant])
  nlinarith [norm_nonneg (radialToLp lower field continuousField)]

def continuousDifferenceCoefficient {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : C(ClosedDisk, ComplexEuclidean dimension)) (radius : ℝ) : ComplexEuclidean dimension :=
  angularCoefficient (fun angle => continuousDifferenceQuotient lower positive bounded field (radius, angle)) mode

theorem continuousDifferenceCoefficient_continuous {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    Continuous (continuousDifferenceCoefficient lower positive bounded mode field) :=
  angularCoefficient_continuous_parameter _ (continuousDifferenceQuotient_continuous lower positive bounded field) mode

theorem continuousDifferenceCoefficient_bound {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : C(ClosedDisk, ComplexEuclidean dimension)) (radius : ℝ) :
    ‖continuousDifferenceCoefficient lower positive bounded mode field radius‖ ≤ (2 / lower) * ‖field‖ :=
  angularCoefficient_sup_bound _ mode _ (mul_nonneg (div_nonneg (by norm_num) positive.le) (norm_nonneg _))
    (fun angle _ => continuousDifferenceQuotient_bound lower positive bounded field (radius, angle))

theorem continuousDifferenceCoefficient_add {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (first second : C(ClosedDisk, ComplexEuclidean dimension)) (radius : ℝ) :
    continuousDifferenceCoefficient lower positive bounded mode (first + second) radius =
      continuousDifferenceCoefficient lower positive bounded mode first radius +
      continuousDifferenceCoefficient lower positive bounded mode second radius := by
  have addition : (fun angle => continuousDifferenceQuotient lower positive bounded (first + second) (radius, angle)) =
      (fun angle => continuousDifferenceQuotient lower positive bounded first (radius, angle)) +
        (fun angle => continuousDifferenceQuotient lower positive bounded second (radius, angle)) := by
    funext angle
    simp only [continuousDifferenceQuotient, ContinuousMap.add_apply, Pi.add_apply]
    rw [add_sub_add_comm, smul_add]
  rw [continuousDifferenceCoefficient, addition]
  exact angularCoefficient_add_continuous _ _
    ((continuousDifferenceQuotient_continuous lower positive bounded first).comp (continuous_const.prodMk continuous_id))
    ((continuousDifferenceQuotient_continuous lower positive bounded second).comp (continuous_const.prodMk continuous_id)) mode

theorem continuousDifferenceCoefficient_smul {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (scalar : ℂ) (field : C(ClosedDisk, ComplexEuclidean dimension)) (radius : ℝ) :
    continuousDifferenceCoefficient lower positive bounded mode (scalar • field) radius =
      scalar • continuousDifferenceCoefficient lower positive bounded mode field radius := by
  have scaling : (fun angle => continuousDifferenceQuotient lower positive bounded (scalar • field) (radius, angle)) =
      scalar • (fun angle => continuousDifferenceQuotient lower positive bounded field (radius, angle)) := by
    funext angle
    simp only [continuousDifferenceQuotient, ContinuousMap.smul_apply, Pi.smul_apply, ← smul_sub]
    exact smul_comm _ _ _
  rw [continuousDifferenceCoefficient, scaling]
  exact angularCoefficient_smul_continuous scalar _ mode

def continuousDifferenceLp {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (mode : ℤ) :
    C(ClosedDisk, ComplexEuclidean dimension) →L[ℂ] RadialL2 dimension lower :=
  LinearMap.mkContinuous
    { toFun := fun field => radialToLp lower (continuousDifferenceCoefficient lower positive bounded mode field)
        (continuousDifferenceCoefficient_continuous lower positive bounded mode field)
      map_add' := fun first second => radialToLp_add_of_interior lower positive _ _ _ _ _ _
        (fun radius _ => continuousDifferenceCoefficient_add lower positive bounded mode first second radius)
      map_smul' := fun scalar field => radialToLp_smul_of_interior lower positive scalar _ _ _ _
        (fun radius _ => continuousDifferenceCoefficient_smul lower positive bounded mode scalar field radius) }
    (2 / lower) (fun field => radialToLp_uniform_bound lower positive.le bounded
      (continuousDifferenceCoefficient lower positive bounded mode field)
      (continuousDifferenceCoefficient_continuous lower positive bounded mode field) _
      (mul_nonneg (div_nonneg (by norm_num) positive.le) (norm_nonneg _))
      (fun radius _ => continuousDifferenceCoefficient_bound lower positive bounded mode field radius))

end Grad.SourceCollarDivision
