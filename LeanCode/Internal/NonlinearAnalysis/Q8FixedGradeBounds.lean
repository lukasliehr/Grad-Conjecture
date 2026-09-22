import Q8FixedGradeMaps

noncomputable section

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace Grad.Q8FixedGrade

open Grad.CartesianState Grad.NonlinearQuotientBounds Grad.CoefficientMajorants

def embedRing (parameters : PhaseParameters) (grade : ℕ) :
    TameCoefficient parameters →+* Carrier parameters grade where
  toFun := embed parameters grade
  map_zero' := map_zero _
  map_one' := embed_one parameters grade
  map_add' := map_add _
  map_mul' := embed_mul parameters grade

theorem embed_prod (parameters : PhaseParameters) (grade order : ℕ)
    (directions : Fin order → TameCoefficient parameters) :
    embed parameters grade (∏ index, directions index) =
      ∏ index, embed parameters grade (directions index) :=
  map_prod (embedRing parameters grade) directions Finset.univ

/-- The literal Q8 coefficient polynomial on the fixed-grade Banach carrier. -/
def coefficientTerm {parameters : PhaseParameters} {grade : ℕ} (p : ℕ)
    (value : Carrier parameters grade) : Carrier parameters grade :=
  (rootCoefficient p : ℂ) • value ^ p

/-- The continuous fixed-grade realization of the accepted Q8 placement term. -/
def derivativeTerm {parameters : PhaseParameters} {grade : ℕ} (order p : ℕ)
    (value : Carrier parameters grade) (directions : Fin order → Carrier parameters grade) :
    Carrier parameters grade :=
  ((rootCoefficient p * (p.descFactorial order : ℝ) : ℝ) : ℂ) •
    (value ^ (p - order) * ∏ index, directions index)

theorem coefficientTerm_embed (parameters : PhaseParameters) (grade p : ℕ)
    (value : TameCoefficient parameters) :
    coefficientTerm p (embed parameters grade value) =
      embed parameters grade ((rootCoefficient p : ℂ) • value ^ p) := by
  rw [map_smul, embed_pow]
  rfl

theorem derivativeTerm_embed (parameters : PhaseParameters) (grade order p : ℕ)
    (value : TameCoefficient parameters) (directions : Fin order → TameCoefficient parameters) :
    derivativeTerm order p (embed parameters grade value)
        (fun index => embed parameters grade (directions index)) =
      embed parameters grade (rootDerivativeTerm order p value directions) := by
  rw [rootDerivativeTerm, map_smul, embed_mul, embed_pow, embed_prod]
  rfl

/-- The all-orders placement bound extends in the original norm to the completion.
This is a bound for the explicit polynomial term; its derivative identity is separate. -/
theorem derivativeTerm_norm_le (parameters : PhaseParameters) (grade order p : ℕ)
    (value : Carrier parameters grade) (directions : Fin order → Carrier parameters grade) :
    ‖derivativeTerm order p value directions‖ ≤
      rootOperatorMajorant parameters grade order (lowNorm parameters grade value) ‖value‖ p *
        ∏ index, ‖directions index‖ := by
  let statement : Carrier parameters grade × (Fin order → Carrier parameters grade) → Prop :=
    fun data => ‖derivativeTerm order p data.1 data.2‖ ≤
      rootOperatorMajorant parameters grade order (lowNorm parameters grade data.1) ‖data.1‖ p *
        ∏ index, ‖data.2 index‖
  have denseDirections : DenseRange
      (fun data : Fin order → TameCoefficient parameters =>
        fun index => embed parameters grade (data index)) :=
    DenseRange.piMap (fun _ => embed_denseRange parameters grade)
  have densePairs := (embed_denseRange parameters grade).prodMap denseDirections
  apply densePairs.induction_on (value, directions)
    (p := statement)
  · dsimp [statement]
    apply isClosed_le
    · unfold derivativeTerm
      exact (((continuous_fst.pow (p - order)).mul
        (continuous_finsetProd Finset.univ (fun index _ =>
          (continuous_apply index).comp continuous_snd))).const_smul
          (((rootCoefficient p * (p.descFactorial order : ℝ) : ℝ) : ℂ))).norm
    · have lowContinuous : Continuous
          (fun data : Carrier parameters grade × (Fin order → Carrier parameters grade) =>
            lowNorm parameters grade data.1) :=
        ((lowerMap parameters (Nat.zero_le grade)).continuous.comp continuous_fst).norm
      have highContinuous : Continuous
          (fun data : Carrier parameters grade × (Fin order → Carrier parameters grade) =>
            ‖data.1‖) := continuous_fst.norm
      have directionContinuous : Continuous
          (fun data : Carrier parameters grade × (Fin order → Carrier parameters grade) =>
            ∏ index, ‖data.2 index‖) :=
        continuous_finsetProd Finset.univ (fun index _ =>
          ((continuous_apply index).comp continuous_snd).norm)
      exact ((continuous_const.mul continuous_const).mul
        (continuous_const.mul
          (((continuous_const.mul (highContinuous.add continuous_const)).mul
              (lowContinuous.pow (p - order - 1))).add
            (continuous_const.mul (lowContinuous.pow (p - order)))))).mul directionContinuous
  · rintro ⟨coreValue, coreDirections⟩
    change ‖derivativeTerm order p (embed parameters grade coreValue)
      (fun index => embed parameters grade (coreDirections index))‖ ≤ _
    rw [derivativeTerm_embed, embed_norm]
    change coefficientEnvelope grade (rootDerivativeTerm order p coreValue coreDirections) ≤
      rootOperatorMajorant parameters grade order
        (lowNorm parameters grade (embed parameters grade coreValue))
        ‖embed parameters grade coreValue‖ p * ∏ index, ‖embed parameters grade (coreDirections index)‖
    simp_rw [lowNorm_embed, embed_norm]
    exact rootDerivativeTerm_envelope_le grade order p
      (coefficientEnvelope_nonneg 0 coreValue) (coefficientEnvelope_nonneg grade coreValue)
      le_rfl le_rfl coreDirections

theorem rootOperatorMajorant_mono (parameters : PhaseParameters) (grade order p : ℕ)
    {theta theta' radius radius' : ℝ} (thetaNonneg : 0 ≤ theta)
    (radiusNonneg : 0 ≤ radius) (thetaLe : theta ≤ theta') (radiusLe : radius ≤ radius') :
    rootOperatorMajorant parameters grade order theta radius p ≤
    rootOperatorMajorant parameters grade order theta' radius' p := by
  unfold rootOperatorMajorant
  have radiusNonneg' : 0 ≤ radius' := radiusNonneg.trans radiusLe
  gcongr

theorem derivativeTerm_norm_le_on_ball (parameters : PhaseParameters) (grade order p : ℕ)
    {theta radius : ℝ} {value : Carrier parameters grade}
    (lowBound : lowNorm parameters grade value ≤ theta) (highBound : ‖value‖ ≤ radius)
    (directions : Fin order → Carrier parameters grade) :
    ‖derivativeTerm order p value directions‖ ≤
      rootOperatorMajorant parameters grade order theta radius p * ∏ index, ‖directions index‖ :=
  (derivativeTerm_norm_le parameters grade order p value directions).trans
    (mul_le_mul_of_nonneg_right
      (rootOperatorMajorant_mono parameters grade order p (norm_nonneg _) (norm_nonneg _)
        lowBound highBound) (Finset.prod_nonneg fun _ _ => norm_nonneg _))

end Grad.Q8FixedGrade
