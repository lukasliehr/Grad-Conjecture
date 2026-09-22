import RSC9CanonicalRestriction

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceCollarRestriction
open Grad.SourceCollarDivision Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace

def continuousPolarValue {dimension : ℕ} (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) (point : ℝ × ℝ) : ComplexEuclidean dimension :=
  field (annularClosedPoint lower positive bounded point)

theorem continuousPolarValue_continuous {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    Continuous (continuousPolarValue lower positive bounded field) :=
  field.continuous.comp (annularClosedPoint_continuous lower positive bounded)

theorem continuousPolarValue_bound {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) (point : ℝ × ℝ) :
    ‖continuousPolarValue lower positive bounded field point‖ ≤ (1 : ℝ) * ‖field‖ := by
  simpa only [continuousPolarValue, one_mul] using ContinuousMap.norm_coe_le_norm field (annularClosedPoint lower positive bounded point)

def continuousPolarCoefficient {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : C(ClosedDisk, ComplexEuclidean dimension)) (radius : ℝ) : ComplexEuclidean dimension :=
  angularCoefficient (fun angle => continuousPolarValue lower positive bounded field (radius, angle)) mode

theorem continuousPolarCoefficient_continuous {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    Continuous (continuousPolarCoefficient lower positive bounded mode field) :=
  angularCoefficient_continuous_parameter _ (continuousPolarValue_continuous lower positive bounded field) mode

theorem continuousPolarCoefficient_bound {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : C(ClosedDisk, ComplexEuclidean dimension)) (radius : ℝ) :
    ‖continuousPolarCoefficient lower positive bounded mode field radius‖ ≤ (1 : ℝ) * ‖field‖ :=
  angularCoefficient_sup_bound _ mode _ (mul_nonneg (by norm_num) (norm_nonneg _))
    (fun angle _ => continuousPolarValue_bound lower positive bounded field (radius, angle))

theorem continuousPolarCoefficient_add {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (first second : C(ClosedDisk, ComplexEuclidean dimension)) (radius : ℝ) :
    continuousPolarCoefficient lower positive bounded mode (first + second) radius =
      continuousPolarCoefficient lower positive bounded mode first radius +
      continuousPolarCoefficient lower positive bounded mode second radius := by
  have addition : (fun angle => continuousPolarValue lower positive bounded (first + second) (radius, angle)) =
      (fun angle => continuousPolarValue lower positive bounded first (radius, angle)) +
        (fun angle => continuousPolarValue lower positive bounded second (radius, angle)) := by
    funext angle
    simp only [continuousPolarValue, ContinuousMap.add_apply, Pi.add_apply]

  rw [continuousPolarCoefficient, addition]
  exact angularCoefficient_add_continuous _ _
    ((continuousPolarValue_continuous lower positive bounded first).comp (continuous_const.prodMk continuous_id))
    ((continuousPolarValue_continuous lower positive bounded second).comp (continuous_const.prodMk continuous_id)) mode

theorem continuousPolarCoefficient_smul {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (scalar : ℂ) (field : C(ClosedDisk, ComplexEuclidean dimension)) (radius : ℝ) :
    continuousPolarCoefficient lower positive bounded mode (scalar • field) radius =
      scalar • continuousPolarCoefficient lower positive bounded mode field radius := by
  have scaling : (fun angle => continuousPolarValue lower positive bounded (scalar • field) (radius, angle)) =
      scalar • (fun angle => continuousPolarValue lower positive bounded field (radius, angle)) := by
    rfl
  rw [continuousPolarCoefficient, scaling]
  exact angularCoefficient_smul_continuous scalar _ mode

def continuousPolarLp {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (mode : ℤ) :
    C(ClosedDisk, ComplexEuclidean dimension) →L[ℂ] RadialL2 dimension lower :=
  LinearMap.mkContinuous
    { toFun := fun field => radialToLp lower (continuousPolarCoefficient lower positive bounded mode field)
        (continuousPolarCoefficient_continuous lower positive bounded mode field)
      map_add' := fun first second => radialToLp_add_of_interior lower positive _ _ _ _ _ _
        (fun radius _ => continuousPolarCoefficient_add lower positive bounded mode first second radius)
      map_smul' := fun scalar field => radialToLp_smul_of_interior lower positive scalar _ _ _ _
        (fun radius _ => continuousPolarCoefficient_smul lower positive bounded mode scalar field radius) }
    (1 : ℝ) (fun field => radialToLp_uniform_bound lower positive.le bounded
      (continuousPolarCoefficient lower positive bounded mode field)
      (continuousPolarCoefficient_continuous lower positive bounded mode field) _
      (mul_nonneg (by norm_num) (norm_nonneg _))
      (fun radius _ => continuousPolarCoefficient_bound lower positive bounded mode field radius))

end Grad.SourceCollarRestriction
