import OrthogonalPullback
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Normed.Operator.NormedSpace

noncomputable section

open MeasureTheory Grad.PDEBootstrap

namespace Grad.KernelPullback.Domain

abbrev DomainL2 (Value : Type*) [NormedAddCommGroup Value] (domain : Set Spatial) :=
  Lp Value 2 ((volume : Measure Spatial).restrict domain)

def Invariant (domain : Set Spatial) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) : Prop :=
  ∀ point : Spatial, orthogonal point ∈ domain ↔ point ∈ domain

abbrev PullbackFamily (Value : Type*) [NormedAddCommGroup Value] [NormedSpace ℂ Value] :=
  (domain : Set Spatial) → MeasurableSet domain →
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) → Invariant domain orthogonal →
      (DomainL2 Value domain ≃ₗᵢ[ℂ] DomainL2 Value domain)

def measureTransport (Value : Type*) [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    {source target : Measure Spatial} (equality : source = target) :
    Lp Value 2 source ≃ₗᵢ[ℂ] Lp Value 2 target := by
  subst target
  exact LinearIsometryEquiv.refl ℂ (Lp Value 2 source)

def univToVolume (Value : Type*) [NormedAddCommGroup Value] [NormedSpace ℂ Value] :
    DomainL2 Value Set.univ ≃ₗᵢ[ℂ] Lp Value 2 (volume : Measure Spatial) :=
  measureTransport Value Measure.restrict_univ

structure PullbackLaws (Value : Type*) [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (pullback : PullbackFamily Value) : Prop where
  measure_preserving : ∀ (domain : Set Spatial), MeasurableSet domain →
    ∀ orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial, Invariant domain orthogonal →
      MeasurePreserving orthogonal ((volume : Measure Spatial).restrict domain)
        ((volume : Measure Spatial).restrict domain)
  invariant_refl : ∀ domain : Set Spatial,
    Invariant domain (LinearIsometryEquiv.refl ℝ Spatial)
  invariant_symm : ∀ (domain : Set Spatial) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial),
    Invariant domain orthogonal → Invariant domain orthogonal.symm
  invariant_trans : ∀ (domain : Set Spatial) (first second : Spatial ≃ₗᵢ[ℝ] Spatial),
    Invariant domain first → Invariant domain second → Invariant domain (first.trans second)
  apply_ae : ∀ (domain : Set Spatial) (measurable : MeasurableSet domain)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (invariant : Invariant domain orthogonal)
    (field : DomainL2 Value domain),
      (pullback domain measurable orthogonal invariant field : Spatial → Value) =ᵐ[
        (volume : Measure Spatial).restrict domain] fun point => field (orthogonal point)
  symm_apply_ae : ∀ (domain : Set Spatial) (measurable : MeasurableSet domain)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (invariant : Invariant domain orthogonal)
    (field : DomainL2 Value domain),
      ((pullback domain measurable orthogonal invariant).symm field : Spatial → Value) =ᵐ[
        (volume : Measure Spatial).restrict domain] fun point => field (orthogonal.symm point)
  symm_eq : ∀ (domain : Set Spatial) (measurable : MeasurableSet domain)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (invariant : Invariant domain orthogonal)
    (inverseInvariant : Invariant domain orthogonal.symm),
      (pullback domain measurable orthogonal invariant).symm =
        pullback domain measurable orthogonal.symm inverseInvariant
  refl_eq : ∀ (domain : Set Spatial) (measurable : MeasurableSet domain)
    (invariant : Invariant domain (LinearIsometryEquiv.refl ℝ Spatial)),
      pullback domain measurable (LinearIsometryEquiv.refl ℝ Spatial) invariant =
        LinearIsometryEquiv.refl ℂ (DomainL2 Value domain)
  trans_eq : ∀ (domain : Set Spatial) (measurable : MeasurableSet domain)
    (first second : Spatial ≃ₗᵢ[ℝ] Spatial)
    (firstInvariant : Invariant domain first) (secondInvariant : Invariant domain second)
    (compositionInvariant : Invariant domain (first.trans second)),
      pullback domain measurable (first.trans second) compositionInvariant =
        (pullback domain measurable second secondInvariant).trans
          (pullback domain measurable first firstInvariant)
  norm_map : ∀ (domain : Set Spatial) (measurable : MeasurableSet domain)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (invariant : Invariant domain orthogonal)
    (field : DomainL2 Value domain), ‖pullback domain measurable orthogonal invariant field‖ = ‖field‖
  opNorm_le : ∀ (domain : Set Spatial) (measurable : MeasurableSet domain)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (invariant : Invariant domain orthogonal),
      ‖(pullback domain measurable orthogonal invariant).toLinearIsometry.toContinuousLinearMap‖ ≤ 1
  opNorm_eq_one : ∀ (domain : Set Spatial) (measurable : MeasurableSet domain)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (invariant : Invariant domain orthogonal),
      Nontrivial (DomainL2 Value domain) →
        ‖(pullback domain measurable orthogonal invariant).toLinearIsometry.toContinuousLinearMap‖ = 1
  opNorm_eq_zero : ∀ (domain : Set Spatial) (measurable : MeasurableSet domain)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (invariant : Invariant domain orthogonal),
      Subsingleton (DomainL2 Value domain) →
        ‖(pullback domain measurable orthogonal invariant).toLinearIsometry.toContinuousLinearMap‖ = 0
  univ_apply : ∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : Invariant Set.univ orthogonal) (field : DomainL2 Value Set.univ),
      univToVolume Value (pullback Set.univ MeasurableSet.univ orthogonal invariant field) =
        Lp.compMeasurePreserving orthogonal orthogonal.measurePreserving (univToVolume Value field)

def constructorGoal (Value : Type*) [NormedAddCommGroup Value] [NormedSpace ℂ Value] : Prop :=
  ∃ pullback : PullbackFamily Value, PullbackLaws Value pullback

end Grad.KernelPullback.Domain
