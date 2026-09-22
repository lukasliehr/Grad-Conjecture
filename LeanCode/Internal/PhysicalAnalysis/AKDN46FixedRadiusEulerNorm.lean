import AKDN42ActualKappaPrimitiveEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate

section Radius
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A fixed radius factor has the same Euler jet at every order. It uses
only lower input derivatives and no additional coefficient rank. -/
theorem radiusMapping_EulerBound (mapping : E →L[ℝ] F) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (curve : ℝ → E) (rank : ℕ)
    (smooth : ContDiffOn ℝ rank curve (Icc lower 1))
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    ‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (fun point => point • mapping (curve point)) radius‖ ≤
      ‖mapping‖*eulerAllocationSum
        (fun _ inputRank => ‖vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank curve radius‖)
        (eulerLeibnizTerms rank) := by
  let operators := fun point : ℝ => (0 : E →L[ℝ] F)+point • mapping
  let applyMap : (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F := (ContinuousLinearMap.apply ℝ F).flip
  have operatorSmooth : ContDiffOn ℝ rank operators (Icc lower 1) :=
    contDiffOn_const.add (contDiffOn_id.smul contDiffOn_const)
  have actual := vectorEulerWithin_bilinear applyMap (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (fun point member => (positive.trans_le member.1).ne') operators curve rank operatorSmooth smooth inside
  have formula : (fun point => applyMap (operators point) (curve point)) =
      (fun point => point • mapping (curve point)) := by
    funext point
    change ((0 : E →L[ℝ] F)+point • mapping) (curve point)=_
    simp only [zero_add,smul_apply]
  rw [formula] at actual
  rw [actual,eulerAllocationSum_mul_left]
  apply (bilinearEulerPolynomial_norm applyMap _ _ _ radius).trans
  apply eulerAllocationSum_mono
  intro term _
  change ‖vectorEulerWithinIteratedDerivative (Icc lower 1) term.1 operators radius
    (vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 curve radius)‖ ≤ _
  rw [affineEulerJets_fidelity (0 : E →L[ℝ] F) mapping (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (fun point member => (positive.trans_le member.1).ne') term.1 radius inside]
  have operatorBound := affineEulerJets_bound (0 : E →L[ℝ] F) mapping term.1
    ⟨radius,⟨positive.le.trans inside.1,inside.2⟩⟩
  simp only [norm_zero,zero_add] at operatorBound
  exact ((affineEulerJets (0 : E →L[ℝ] F) mapping term.1 radius).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right operatorBound (norm_nonneg _))

theorem radiusMapping_weightedEulerBound (mapping : E →L[ℝ] F) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (curve : ℝ → E) (rank : ℕ)
    (smooth : ContDiffOn ℝ rank curve (Icc lower 1)) (weight : ℝ) (weight0 : 0 ≤ weight)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    ‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (fun point => point • mapping (curve point)) radius‖ ≤
      ‖mapping‖*eulerAllocationSum
        (fun _ inputRank => ‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank curve radius‖)
        (eulerLeibnizTerms rank) := by
  have actual := mul_le_mul_of_nonneg_left
    (radiusMapping_EulerBound mapping lower positive bounded curve rank smooth radius inside) weight0
  simp only [norm_smul,Real.norm_of_nonneg weight0]
  rw [← eulerAllocationSum_mul_left]
  nlinarith only [actual]

end Radius
end Grad.OriginalCartesianTameEstimate
