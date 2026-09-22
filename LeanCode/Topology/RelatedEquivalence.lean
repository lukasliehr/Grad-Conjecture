import ReparametrizationEmbeddingConsumer
import Mathlib.Tactic.Module

noncomputable section

namespace Grad.MainAssembly.TargetRelation

open Grad.MainTarget
open Grad.MainAssembly.TargetReparametrization

/-- Reflexivity of the literal full target relation. -/
theorem related_refl (regularity : Regularity)
    (configuration : Configuration regularity) :
    Related regularity configuration configuration := by
  refine ⟨1, 1, LinearIsometryEquiv.refl ℝ Vec, 0, 0,
    Equiv.refl Reference, one_pos, one_ne_zero,
    identityIsReparametrization regularity, ?_⟩
  intro point
  simp

/-- Symmetry with the exact inverse scale, orthogonal map, affine offsets,
amplitude and reference reparametrization. -/
theorem related_symm (regularity : Regularity)
    {first second : Configuration regularity}
    (relation : Related regularity first second) :
    Related regularity second first := by
  rcases relation with
    ⟨spatialScale, amplitude, orthogonal, translation, pressureOffset,
      reparametrization, spatialScalePositive, amplitudeNonzero,
      reparametrizationRegular, pointwise⟩
  refine ⟨spatialScale⁻¹, amplitude⁻¹, orthogonal.symm,
    -(spatialScale⁻¹ • orthogonal.symm translation),
    -((amplitude⁻¹) ^ 2 * pressureOffset), reparametrization.symm,
    inv_pos.mpr spatialScalePositive, inv_ne_zero amplitudeNonzero,
    inverseIsReparametrization regularity reparametrization
      reparametrizationRegular, ?_⟩
  intro point
  have equations := pointwise (reparametrization.symm point)
  simp only [Equiv.apply_symm_apply] at equations
  refine ⟨?_, ?_, ?_⟩
  · rw [equations.1]
    simp only [map_add, map_smul, LinearIsometryEquiv.symm_apply_apply]
    symm
    calc
      _ = (spatialScale⁻¹ * spatialScale) •
          first.val.position point := by module
      _ = first.val.position point := by
        rw [inv_mul_cancel₀ spatialScalePositive.ne']
        simp
  · rw [equations.2.1]
    simp only [map_smul, LinearIsometryEquiv.symm_apply_apply]
    symm
    calc
      _ = (amplitude⁻¹ * amplitude) • first.val.magnetic point := by module
      _ = first.val.magnetic point := by
        rw [inv_mul_cancel₀ amplitudeNonzero]
        simp
  · rw [equations.2.2]
    field_simp [amplitudeNonzero]
    ring

/-- Transitivity with the exact composed affine and pressure parameters. -/
theorem related_trans (regularity : Regularity)
    {first second third : Configuration regularity}
    (firstSecond : Related regularity first second)
    (secondThird : Related regularity second third) :
    Related regularity first third := by
  rcases firstSecond with
    ⟨firstScale, firstAmplitude, firstOrthogonal, firstTranslation,
      firstPressureOffset, firstReparametrization, firstScalePositive,
      firstAmplitudeNonzero, firstReparametrizationRegular, firstPointwise⟩
  rcases secondThird with
    ⟨secondScale, secondAmplitude, secondOrthogonal, secondTranslation,
      secondPressureOffset, secondReparametrization, secondScalePositive,
      secondAmplitudeNonzero, secondReparametrizationRegular, secondPointwise⟩
  refine ⟨secondScale * firstScale, secondAmplitude * firstAmplitude,
    firstOrthogonal.trans secondOrthogonal,
    secondScale • secondOrthogonal firstTranslation + secondTranslation,
    secondAmplitude ^ 2 * firstPressureOffset + secondPressureOffset,
    secondReparametrization.trans firstReparametrization,
    mul_pos secondScalePositive firstScalePositive,
    mul_ne_zero secondAmplitudeNonzero firstAmplitudeNonzero,
    compIsReparametrization regularity firstReparametrization
      secondReparametrization firstReparametrizationRegular
      secondReparametrizationRegular, ?_⟩
  intro point
  have outerEquations := secondPointwise point
  have innerEquations := firstPointwise (secondReparametrization point)
  refine ⟨?_, ?_, ?_⟩
  · rw [outerEquations.1, innerEquations.1]
    simp only [Equiv.trans_apply, LinearIsometryEquiv.trans_apply, map_add,
      map_smul]
    module
  · rw [outerEquations.2.1, innerEquations.2.1]
    simp only [Equiv.trans_apply, LinearIsometryEquiv.trans_apply, map_smul]
    module
  · rw [outerEquations.2.2, innerEquations.2.2]
    simp only [Equiv.trans_apply]
    ring

def relatedSetoid (regularity : Regularity) : Setoid (Configuration regularity) where
  r := Related regularity
  iseqv := ⟨related_refl regularity, related_symm regularity,
    related_trans regularity⟩

theorem related_of_eqvGen (regularity : Regularity)
    {first second : Configuration regularity}
    (generated : Relation.EqvGen (Related regularity) first second) :
    Related regularity first second := by
  induction generated with
  | rel first second relation => exact relation
  | refl configuration => exact related_refl regularity configuration
  | symm first second _ inductionHypothesis =>
      exact related_symm regularity inductionHypothesis
  | trans first second third _ _ firstInduction secondInduction =>
      exact related_trans regularity firstInduction secondInduction

/-- Equality in the target's actual generated `Quot` is exactly one step of
the full relation because that relation is already an equivalence. -/
theorem moduliClass_eq_iff_related (regularity : Regularity)
    (first second : Configuration regularity) :
    moduliClass regularity first = moduliClass regularity second ↔
      Related regularity first second := by
  change Quot.mk (Related regularity) first =
      Quot.mk (Related regularity) second ↔ _
  rw [Quot.eq]
  exact ⟨related_of_eqvGen regularity, Relation.EqvGen.rel _ _⟩

/-- The target's generated `Quot` and the associated Setoid quotient are
canonically equivalent once the exact closure laws have been proved. -/
def moduliEquivRelatedQuotient (regularity : Regularity) :
    Moduli regularity ≃ Quotient (relatedSetoid regularity) where
  toFun := Quot.lift
    (fun configuration => Quotient.mk (relatedSetoid regularity) configuration)
    (fun _ _ relation =>
      @Quotient.sound _ (relatedSetoid regularity) _ _ relation)
  invFun := Quotient.lift
    (fun configuration => moduliClass regularity configuration)
    (fun _ _ relation => Quot.sound relation)
  left_inv quotient := by
    induction quotient using Quot.ind with
    | _ configuration => rfl
  right_inv quotient := by
    induction quotient using Quotient.inductionOn with
    | _ configuration => rfl

end Grad.MainAssembly.TargetRelation
