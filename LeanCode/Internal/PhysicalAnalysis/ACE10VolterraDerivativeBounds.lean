import ACE9PolynomialDerivativeMajorant

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

def sourceDerivativeEnvelope {dimension : ℕ} (grade : ℕ) (field : ClosedJet dimension) : ℝ :=
  1 + ∑ order ∈ Finset.range (grade + 1), ∑ word : CartesianWord order,
    ‖spatialPlaneWordCoefficient word‖ * ‖closedDerivative field order word‖

theorem sourceDerivativeEnvelope_one_le {dimension : ℕ} (grade : ℕ) (field : ClosedJet dimension) :
    1 ≤ sourceDerivativeEnvelope grade field := by
  unfold sourceDerivativeEnvelope
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))))

theorem sourceDerivativeEnvelope_bound {dimension : ℕ} (grade order : ℕ) (upper : order ≤ grade)
    (field : ClosedJet dimension) :
    (∑ word : CartesianWord order, ‖spatialPlaneWordCoefficient word‖ *
      ‖closedDerivative field order word‖) ≤ sourceDerivativeEnvelope grade field := by
  have one := Finset.single_le_sum
    (f := fun order => ∑ word : CartesianWord order,
      ‖spatialPlaneWordCoefficient word‖ * ‖closedDerivative field order word‖)
    (fun _ _ => Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (Finset.mem_range.mpr (by omega : order < grade + 1))
  unfold sourceDerivativeEnvelope
  linarith

theorem positiveKernel_operator_bound {dimension : ℕ} (grade count order : ℕ) (upper : order ≤ grade)
    (field : ClosedJet dimension) (point : ClosedDisk) :
    ‖iteratedFDeriv ℝ order (smoothClosedExtension (positiveKernel count field)) point.val‖ ≤
      kernelMass count * sourceDerivativeEnvelope grade field := by
  apply (jetOperatorDerivative_point_bound (positiveKernel count field) point).trans
  calc
    _ ≤ ∑ word : CartesianWord order, ‖spatialPlaneWordCoefficient word‖ *
        (kernelMass count * ‖closedDerivative field order word‖) := by
      apply Finset.sum_le_sum
      intro word _
      exact mul_le_mul_of_nonneg_left
        ((ContinuousMap.norm_coe_le_norm _ point).trans (positiveKernel_derivative_norm count field word))
        (norm_nonneg _)
    _ = kernelMass count * ∑ word : CartesianWord order,
        ‖spatialPlaneWordCoefficient word‖ * ‖closedDerivative field order word‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro word _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sourceDerivativeEnvelope_bound grade order upper field)
      (kernelMass_positive count).le

/-- A smooth ambient representative for each actual Volterra iterate. Its
restriction is exact; the chosen extensions are used only to construct jets. -/
def volterraPowerValue {dimension : ℕ} (count : ℕ) (field : ClosedJet dimension) :
    SpatialPlane → ComplexEuclidean dimension := radiusPowerValue count (positiveKernel count field)

theorem volterraPowerValue_smooth {dimension : ℕ} (count : ℕ) (field : ClosedJet dimension) :
    ContDiff ℝ ∞ (volterraPowerValue count field) := radiusPowerValue_smooth _ _

theorem volterraPowerValue_value {dimension : ℕ} (count : ℕ) (field : ClosedJet dimension)
    (point : ClosedDisk) : volterraPowerValue count field point.val = (volterraPower count field).value point := by
  rw [volterraPower_kernel]
  rfl

def volterraPowerMajorant {dimension : ℕ} (grade count : ℕ) (field : ClosedJet dimension) : ℝ :=
  leibnizEnvelope grade * sourceDerivativeEnvelope grade field *
    radiusIterationConstant grade ^ count * kernelMass count

theorem volterraPower_operator_bound {dimension : ℕ} (grade count order : ℕ) (upper : order ≤ grade)
    (field : ClosedJet dimension) (point : ClosedDisk) :
    ‖iteratedFDeriv ℝ order (volterraPowerValue count field) point.val‖ ≤
      volterraPowerMajorant grade count field := by
  have constantNonnegative : 0 ≤ radiusIterationConstant grade :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (radiusIterationConstant_one_le grade)
  have sourceNonnegative : 0 ≤ sourceDerivativeEnvelope grade field :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (sourceDerivativeEnvelope_one_le grade field)
  have product := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (N := ∞) (n := order)
    (radiusSquare_smooth.pow count) (smoothClosedExtension_smooth (positiveKernel count field)) point.val
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  apply product.trans
  calc
    _ ≤ ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
        radiusIterationConstant grade ^ count * (kernelMass count * sourceDerivativeEnvelope grade field) := by
      apply Finset.sum_le_sum
      intro index inside
      have indexUpper : index ≤ grade := by have := Finset.mem_range.mp inside; omega
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (radiusPower_operator_bound grade count index indexUpper point)
          (Nat.cast_nonneg _))
        (positiveKernel_operator_bound grade count (order - index) ((Nat.sub_le _ _).trans upper) field point)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg constantNonnegative _))
    _ = (∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ)) *
        radiusIterationConstant grade ^ count * (kernelMass count * sourceDerivativeEnvelope grade field) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ leibnizEnvelope grade * radiusIterationConstant grade ^ count *
        (kernelMass count * sourceDerivativeEnvelope grade field) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (leibnizEnvelope_bound grade order upper)
        (pow_nonneg constantNonnegative _)) (mul_nonneg (kernelMass_positive _).le sourceNonnegative)
    _ = _ := by unfold volterraPowerMajorant; ring

end Grad.ActualCenterVolterra
