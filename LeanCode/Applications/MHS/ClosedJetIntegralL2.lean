import ClosedJetOrthogonalL2
import FP17Decay
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace Grad.Constraints

open Grad.ClosedJets Grad.CartesianState

theorem closedValueL2_norm_le {dimension : ℕ}
    (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    ‖closedContinuousToDiskL2 field‖ ≤
      Real.sqrt ((volume.restrict openUnitDisk).real univ) * ‖field‖ := by
  have squareBound := closedContinuousToDiskL2_norm_sq_le field
  have massNonnegative : 0 ≤ (volume.restrict openUnitDisk).real univ := measureReal_nonneg
  have rootSquare := Real.sq_sqrt massNonnegative
  have rootNonnegative := Real.sqrt_nonneg ((volume.restrict openUnitDisk).real univ)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg rootNonnegative (norm_nonneg _))).mp
  rw [mul_pow, rootSquare]
  exact squareBound

/-- The literal continuous-function-to-disk-L2 map, not a replacement norm. -/
def closedValueL2Continuous (dimension : ℕ) :
    C(ClosedDisk, ComplexEuclidean dimension) →L[ℂ] DiskL2 dimension :=
  (closedValueL2Linear dimension).mkContinuous
    (Real.sqrt ((volume.restrict openUnitDisk).real univ)) closedValueL2_norm_le

theorem closedValueL2_real_smul {dimension : ℕ} (scalar : ℝ)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    closedContinuousToDiskL2 (scalar • field) = scalar • closedContinuousToDiskL2 field :=
  ((closedValueL2Continuous dimension).restrictScalars ℝ).map_smul scalar field

theorem closedValueL2_integral {dimension : ℕ}
    {family : ℝ → C(ClosedDisk, ComplexEuclidean dimension)} {lower upper : ℝ}
    (integrable : IntegrableOn family (Icc lower upper)) :
    closedContinuousToDiskL2 (∫ angle in Icc lower upper, family angle) =
      ∫ angle in Icc lower upper, closedContinuousToDiskL2 (family angle) := by
  exact ((closedValueL2Continuous dimension).integral_comp_comm integrable).symm

theorem closedValueL2_integral_norm_le {dimension : ℕ}
    {family : ℝ → C(ClosedDisk, ComplexEuclidean dimension)} {lower upper bound : ℝ}
    (continuous : Continuous family)
    (bounded : ∀ angle ∈ Icc lower upper, ‖closedContinuousToDiskL2 (family angle)‖ ≤ bound) :
    ‖closedContinuousToDiskL2 (∫ angle in Icc lower upper, family angle)‖ ≤
      (volume.real (Icc lower upper)) * bound := by
  rw [closedValueL2_integral continuous.continuousOn.integrableOn_Icc]
  have l2Continuous := (closedValueL2Continuous dimension).continuous.comp continuous
  calc
    _ ≤ ∫ angle in Icc lower upper, ‖closedContinuousToDiskL2 (family angle)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _angle in Icc lower upper, bound := by
      apply setIntegral_mono_on l2Continuous.norm.continuousOn.integrableOn_Icc
        continuous_const.continuousOn.integrableOn_Icc measurableSet_Icc bounded
    _ = _ := by rw [setIntegral_const]; rfl

theorem closedValueL2_normalized_integral_norm_le {dimension : ℕ}
    {family : ℝ → C(ClosedDisk, ComplexEuclidean dimension)} {bound : ℝ}
    (continuous : Continuous family)
    (bounded : ∀ angle ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖closedContinuousToDiskL2 (family angle)‖ ≤ bound) :
    ‖closedContinuousToDiskL2
      (((2 * Real.pi)⁻¹ : ℝ) • ∫ angle in Icc (0 : ℝ) (2 * Real.pi), family angle)‖ ≤ bound := by
  have periodPositive : 0 < 2 * Real.pi := by positivity
  have mass : volume.real (Icc (0 : ℝ) (2 * Real.pi)) = 2 * Real.pi := by
    simp [Measure.real, Real.volume_Icc, Real.pi_pos.le]
  rw [closedValueL2_real_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr periodPositive.le)]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (volume.real (Icc (0 : ℝ) (2 * Real.pi)) * bound) :=
      mul_le_mul_of_nonneg_left (closedValueL2_integral_norm_le continuous bounded)
        (inv_nonneg.mpr periodPositive.le)
    _ = bound := by rw [mass, ← mul_assoc, inv_mul_cancel₀ periodPositive.ne', one_mul]

end Grad.Constraints
