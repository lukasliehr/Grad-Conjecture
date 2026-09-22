import Q8FixedGradeCarrier

noncomputable section

namespace Grad.Q8FixedGrade

open Grad.CartesianState Grad.NonlinearQuotientBounds

def lowerCore (parameters : PhaseParameters) {lower upper : ℕ} (le : lower ≤ upper) :
    Core parameters upper →L[ℂ] Core parameters lower :=
  LinearMap.mkContinuous
    { toFun := fun value => Core.mk value.toCore
      map_add' _ _ := rfl
      map_smul' _ _ := rfl } 1 (fun value => by
        rw [one_mul]
        exact coefficientEnvelope_mono le value.toCore)

/-- The actual fixed-grade inclusion, with the identical coefficient core. -/
def lowerMap (parameters : PhaseParameters) {lower upper : ℕ} (le : lower ≤ upper) :
    Carrier parameters upper →L[ℂ] Carrier parameters lower :=
  (lowerCore parameters le).completion

theorem lowerMap_embed (parameters : PhaseParameters) {lower upper : ℕ}
    (le : lower ≤ upper) (value : TameCoefficient parameters) :
    lowerMap parameters le (embed parameters upper value) = embed parameters lower value :=
  ContinuousLinearMap.completion_apply_coe (lowerCore parameters le) (Core.mk value)

theorem lowerMap_norm_le (parameters : PhaseParameters) {lower upper : ℕ}
    (le : lower ≤ upper) (value : Carrier parameters upper) :
    ‖lowerMap parameters le value‖ ≤ ‖value‖ := by
  induction value using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (lowerMap parameters le).continuous.norm continuous_norm
  | ih value =>
      change ‖lowerMap parameters le (embed parameters upper value.toCore)‖ ≤
        ‖embed parameters upper value.toCore‖
      rw [lowerMap_embed, embed_norm, embed_norm]
      exact coefficientEnvelope_mono le value.toCore

theorem lowerMap_mul (parameters : PhaseParameters) {lower upper : ℕ}
    (le : lower ≤ upper) (first second : Carrier parameters upper) :
    lowerMap parameters le (first * second) =
      lowerMap parameters le first * lowerMap parameters le second := by
  induction first, second using UniformSpace.Completion.induction_on₂ with
  | hp =>
      exact isClosed_eq ((lowerMap parameters le).continuous.comp continuous_mul)
        (((lowerMap parameters le).continuous.comp continuous_fst).mul
          ((lowerMap parameters le).continuous.comp continuous_snd))
  | ih first second =>
      change lowerMap parameters le
          (embed parameters upper first.toCore * embed parameters upper second.toCore) =
        lowerMap parameters le (embed parameters upper first.toCore) *
          lowerMap parameters le (embed parameters upper second.toCore)
      rw [← embed_mul, lowerMap_embed, embed_mul, lowerMap_embed, lowerMap_embed]

theorem lowerMap_one (parameters : PhaseParameters) {lower upper : ℕ}
    (le : lower ≤ upper) : lowerMap parameters le 1 = 1 := by
  rw [← embed_one parameters upper, lowerMap_embed, embed_one]

theorem lowerMap_refl (parameters : PhaseParameters) (grade : ℕ) :
    lowerMap parameters (le_refl grade) = ContinuousLinearMap.id ℂ (Carrier parameters grade) := by
  apply ContinuousLinearMap.ext
  intro value
  induction value using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (lowerMap parameters (le_refl grade)).continuous continuous_id
  | ih value => exact lowerMap_embed parameters (le_refl grade) value.toCore

theorem lowerMap_trans (parameters : PhaseParameters) {first second third : ℕ}
    (firstLe : first ≤ second) (secondLe : second ≤ third) :
    (lowerMap parameters firstLe).comp (lowerMap parameters secondLe) =
      lowerMap parameters (firstLe.trans secondLe) := by
  apply ContinuousLinearMap.ext
  intro value
  induction value using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        ((lowerMap parameters firstLe).continuous.comp (lowerMap parameters secondLe).continuous)
        (lowerMap parameters (firstLe.trans secondLe)).continuous
  | ih value =>
      change lowerMap parameters firstLe
        (lowerMap parameters secondLe (embed parameters third value.toCore)) =
          lowerMap parameters (firstLe.trans secondLe) (embed parameters third value.toCore)
      rw [lowerMap_embed, lowerMap_embed, lowerMap_embed]

/-- The original low envelope on a fixed-grade completion. -/
def lowNorm (parameters : PhaseParameters) (grade : ℕ) (value : Carrier parameters grade) : ℝ :=
  ‖lowerMap parameters (Nat.zero_le grade) value‖

theorem lowNorm_embed (parameters : PhaseParameters) (grade : ℕ)
    (value : TameCoefficient parameters) :
    lowNorm parameters grade (embed parameters grade value) = coefficientEnvelope 0 value := by
  rw [lowNorm, lowerMap_embed, embed_norm]

theorem lowNorm_le (parameters : PhaseParameters) (grade : ℕ)
    (value : Carrier parameters grade) : lowNorm parameters grade value ≤ ‖value‖ :=
  lowerMap_norm_le parameters (Nat.zero_le grade) value

end Grad.Q8FixedGrade
