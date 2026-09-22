import Q24AxisComponents
import QU1AxisInclusions

noncomputable section

open scoped ContDiff

namespace Grad.Q24Realization

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearQuotientBounds Grad.AxisCore
open Grad.Q8FixedGrade Grad.ConstrainedGrades

theorem axisLowering_tangent (parameters : PhaseParameters) {lower upper : ℕ}
    (ordered : lower ≤ upper) (family : TangentCoefficient parameters) :
    axisLowering parameters ordered (tangentToGrade parameters upper family) =
      tangentToGrade parameters lower family := by
  change axisLowering parameters ordered (axisEta parameters 2 upper (tangentAxisEquiv parameters family)) =
    axisEta parameters 2 lower (tangentAxisEquiv parameters family)
  rw [← bridgeCore_toGrade, axisLowering_core, bridgeCore_toGrade]

/-- The literal Q8 argument tau dot tau / 2 on the completed axis carrier. -/
def completedTangentQuadratic (parameters : PhaseParameters) (grade : ℕ)
    (family : AxisGrade parameters 2 (grade + 1)) : Carrier parameters grade :=
  (2 : ℂ)⁻¹ •
    (tangentComponentMap parameters grade 0 family * tangentComponentMap parameters grade 0 family +
      tangentComponentMap parameters grade 1 family * tangentComponentMap parameters grade 1 family)

theorem completedTangentQuadratic_core (parameters : PhaseParameters) (grade : ℕ)
    (family : TangentCoefficient parameters) :
    completedTangentQuadratic parameters grade (tangentToGrade parameters (grade + 1) family) =
      embed parameters grade (tangentQuadratic family) := by
  simp only [completedTangentQuadratic, tangentComponentMap_core, tangentQuadratic, tangentDot,
    map_smul, map_add, embed_mul]

theorem completedTangentQuadratic_contDiff (parameters : PhaseParameters) (grade : ℕ) :
    ContDiff ℝ ∞ (completedTangentQuadratic parameters grade) :=
  (((tangentComponentMap parameters grade 0).contDiff.mul
      (tangentComponentMap parameters grade 0).contDiff).add
    ((tangentComponentMap parameters grade 1).contDiff.mul
      (tangentComponentMap parameters grade 1).contDiff)).const_smul ((2 : ℂ)⁻¹)

/-- Original low-axis norm bound, independent of the high grade. -/
theorem completedTangentQuadratic_low_bound (parameters : PhaseParameters) (grade : ℕ)
    (family : AxisGrade parameters 2 (grade + 1)) :
    lowNorm parameters grade (completedTangentQuadratic parameters grade family) ≤
      (axisConstant * ‖axisLowering parameters (show 1 ≤ grade + 1 by omega) family‖) ^ 2 := by
  refine isClosed_property (tangentToGrade_denseRange parameters (grade + 1))
    (isClosed_le ((lowerMap parameters (Nat.zero_le grade)).continuous.comp
      (completedTangentQuadratic_contDiff parameters grade).continuous).norm
      ((continuous_const.mul (axisLowering parameters (show 1 ≤ grade + 1 by omega)).continuous.norm).pow 2))
    ?_ family
  intro core
  change lowNorm parameters grade
    (completedTangentQuadratic parameters grade (tangentToGrade parameters (grade + 1) core)) ≤
      (axisConstant * ‖axisLowering parameters (show 1 ≤ grade + 1 by omega)
        (tangentToGrade parameters (grade + 1) core)‖) ^ 2
  rw [completedTangentQuadratic_core, lowNorm_embed, axisLowering_tangent, tangentToGrade_norm]
  have bridge := tangentPlanarEnvelope_le 0 core
  simp only [pow_zero, one_mul, zero_add] at bridge
  have squared := pow_le_pow_left₀ (tangentPlanarEnvelope_nonneg 0 core) bridge 2
  exact (tangentQuadratic_envelope_zero_le core).trans (by simpa only [pow_two] using squared)

/-- Q13 with its exact original low axis norm and radius. -/
def axisDomain (parameters : PhaseParameters) (grade : ℕ) :
    Set (AxisGrade parameters 2 (grade + 1)) :=
  {family | ‖axisLowering parameters (show 1 ≤ grade + 1 by omega) family‖ < (2 * axisConstant)⁻¹}

theorem axisDomain_isOpen (parameters : PhaseParameters) (grade : ℕ) :
    IsOpen (axisDomain parameters grade) :=
  isOpen_lt (axisLowering parameters (show 1 ≤ grade + 1 by omega)).continuous.norm continuous_const

theorem axisDomain_quadratic_small (parameters : PhaseParameters) (grade : ℕ)
    {family : AxisGrade parameters 2 (grade + 1)} (inside : family ∈ axisDomain parameters grade) :
    completedTangentQuadratic parameters grade family ∈ rootDomain parameters grade := by
  change ‖axisLowering parameters (show 1 ≤ grade + 1 by omega) family‖ < (2 * axisConstant)⁻¹ at inside
  change lowNorm parameters grade (completedTangentQuadratic parameters grade family) < 1
  have lowNonneg := norm_nonneg (axisLowering parameters (show 1 ≤ grade + 1 by omega) family)
  have productLt := mul_lt_mul_of_pos_left inside axisConstant_pos
  have collapse : axisConstant * (2 * axisConstant)⁻¹ = 1 / 2 := by
    field_simp [axisConstant_pos.ne']
  rw [collapse] at productLt
  have productNonneg := mul_nonneg axisConstant_pos.le lowNonneg
  exact (completedTangentQuadratic_low_bound parameters grade family).trans_lt (by nlinarith)

theorem axisDomain_core_iff (parameters : PhaseParameters) (grade : ℕ)
    (family : TangentCoefficient parameters) :
    tangentToGrade parameters (grade + 1) family ∈ axisDomain parameters grade ↔
      tangentNorm 1 family < (2 * axisConstant)⁻¹ := by
  change ‖axisLowering parameters (show 1 ≤ grade + 1 by omega)
    (tangentToGrade parameters (grade + 1) family)‖ < _ ↔ _
  rw [axisLowering_tangent, tangentToGrade_norm]

end Grad.Q24Realization
