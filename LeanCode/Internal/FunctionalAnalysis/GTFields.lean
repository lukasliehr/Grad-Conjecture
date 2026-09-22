import GTProof
import TL2Proof
import DP1DomainPullback

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (Tensor DomainL2)
open scoped BigOperators

namespace Grad.TensorAction.Generic

universe valueUniverse pointUniverse

variable (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
variable {Point : Type pointUniverse} [MeasurableSpace Point] (measure : Measure Point)

theorem covectorAction_lp_ae (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (fields : Tensor rank (Lp Value 2 measure)) :
    ∀ᵐ point ∂measure, ∀ output : Fin rank → Fin 2,
      covectorAction (Lp Value 2 measure) rank orthogonal fields output point =
        covectorAction Value rank orthogonal
          (WithLp.toLp 2 (fun input => fields input point)) output := by
  apply ae_all_iff.mpr
  intro output
  let coefficient (input : Fin rank → Fin 2) : ℂ :=
    TensorCoefficients.tensorCoefficient rank (OrthogonalCoefficients.coefficient orthogonal) output input
  have allScalars : ∀ᵐ point ∂measure, ∀ input : Fin rank → Fin 2,
      (coefficient input • fields input : Lp Value 2 measure) point =
        coefficient input • fields input point :=
    ae_all_iff.mpr (fun input => Lp.coeFn_smul (coefficient input) (fields input))
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun input => coefficient input • fields input), allScalars] with point summed scaled
  change (∑ input, coefficient input • fields input : Lp Value 2 measure) point =
    ∑ input, coefficient input • fields input point
  rw [summed]
  exact Finset.sum_congr rfl (fun input _membership => scaled input)

def pointwiseLpAction (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    Lp (Tensor rank Value) 2 measure →L[ℂ] Lp (Tensor rank Value) 2 measure :=
  (covectorEquivalence Value rank orthogonal).toLinearIsometry.toContinuousLinearMap.compLpL 2 measure

theorem pointwiseLpAction_ae (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : Lp (Tensor rank Value) 2 measure) :
    (pointwiseLpAction Value measure rank orthogonal field : Point → Tensor rank Value) =ᵐ[measure]
      fun point => covectorAction Value rank orthogonal (field point) :=
  (covectorEquivalence Value rank orthogonal).toLinearIsometry.toContinuousLinearMap.coeFn_compLpL field

theorem exchange_covector (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (fields : Tensor rank (Lp Value 2 measure)) :
    Grad.TensorLpExchange.Generic.exchange (Fin rank → Fin 2) Value measure
        (covectorAction (Lp Value 2 measure) rank orthogonal fields) =
      pointwiseLpAction Value measure rank orthogonal
        (Grad.TensorLpExchange.Generic.exchange (Fin rank → Fin 2) Value measure fields) := by
  apply Lp.ext
  filter_upwards [Grad.TensorLpExchange.Generic.collect_ae (Fin rank → Fin 2) Value measure
      (covectorAction (Lp Value 2 measure) rank orthogonal fields),
    Grad.TensorLpExchange.Generic.collect_ae (Fin rank → Fin 2) Value measure fields,
    pointwiseLpAction_ae Value measure rank orthogonal
      (Grad.TensorLpExchange.Generic.exchange (Fin rank → Fin 2) Value measure fields),
    covectorAction_lp_ae Value measure rank orthogonal fields]
    with point exchanged collected acted coordinates
  change Grad.TensorLpExchange.Generic.collect (Fin rank → Fin 2) Value measure
    (covectorAction (Lp Value 2 measure) rank orthogonal fields) point = _
  rw [exchanged, acted]
  change _ = covectorAction Value rank orthogonal
    (Grad.TensorLpExchange.Generic.collect (Fin rank → Fin 2) Value measure fields point)
  rw [collected]
  exact PiLp.ext coordinates

def pointwiseEquivalence (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    Lp (Tensor rank Value) 2 measure ≃ₗᵢ[ℂ] Lp (Tensor rank Value) 2 measure :=
  ((Grad.TensorLpExchange.Generic.exchange (Fin rank → Fin 2) Value measure).symm.trans
    (covectorEquivalence (Lp Value 2 measure) rank orthogonal)).trans
      (Grad.TensorLpExchange.Generic.exchange (Fin rank → Fin 2) Value measure)

theorem pointwiseEquivalence_apply (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : Lp (Tensor rank Value) 2 measure) :
    pointwiseEquivalence Value measure rank orthogonal field =
      pointwiseLpAction Value measure rank orthogonal field := by
  change Grad.TensorLpExchange.Generic.exchange (Fin rank → Fin 2) Value measure
    (covectorAction (Lp Value 2 measure) rank orthogonal
      ((Grad.TensorLpExchange.Generic.exchange (Fin rank → Fin 2) Value measure).symm field)) = _
  rw [exchange_covector, LinearIsometryEquiv.apply_symm_apply]

theorem pointwiseLpAction_norm (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : Lp (Tensor rank Value) 2 measure) :
    ‖pointwiseLpAction Value measure rank orthogonal field‖ = ‖field‖ := by
  rw [← pointwiseEquivalence_apply]
  exact (pointwiseEquivalence Value measure rank orthogonal).norm_map field

variable (domain : Set Spatial) (measurable : MeasurableSet domain)

def entrywisePullback (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : Grad.KernelPullback.Domain.Invariant domain orthogonal) :
    Tensor rank (DomainL2 Value domain) ≃ₗᵢ[ℂ] Tensor rank (DomainL2 Value domain) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin rank → Fin 2 =>
    Grad.KernelPullback.Domain.domainPullback Value domain measurable orthogonal invariant)

theorem entrywisePullback_coordinate (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : Grad.KernelPullback.Domain.Invariant domain orthogonal)
    (fields : Tensor rank (DomainL2 Value domain)) (word : Fin rank → Fin 2) :
    entrywisePullback Value domain measurable rank orthogonal invariant fields word =
      Grad.KernelPullback.Domain.domainPullback Value domain measurable orthogonal invariant (fields word) := rfl

theorem entrywisePullback_ae (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : Grad.KernelPullback.Domain.Invariant domain orthogonal)
    (fields : Tensor rank (DomainL2 Value domain)) :
    ∀ᵐ point ∂volume.restrict domain, ∀ word : Fin rank → Fin 2,
      entrywisePullback Value domain measurable rank orthogonal invariant fields word point =
        fields word (orthogonal point) :=
  ae_all_iff.mpr (fun word =>
    Grad.KernelPullback.Domain.domainPullback_ae Value domain measurable orthogonal invariant (fields word))

theorem entrywisePullback_trans (rank : ℕ) (first second : Spatial ≃ₗᵢ[ℝ] Spatial)
    (firstInvariant : Grad.KernelPullback.Domain.Invariant domain first)
    (secondInvariant : Grad.KernelPullback.Domain.Invariant domain second)
    (compositionInvariant : Grad.KernelPullback.Domain.Invariant domain (first.trans second))
    (fields : Tensor rank (DomainL2 Value domain)) :
    entrywisePullback Value domain measurable rank (first.trans second) compositionInvariant fields =
      entrywisePullback Value domain measurable rank first firstInvariant
        (entrywisePullback Value domain measurable rank second secondInvariant fields) := by
  apply PiLp.ext
  intro word
  exact congrArg (fun mapping : DomainL2 Value domain ≃ₗᵢ[ℂ] DomainL2 Value domain => mapping (fields word))
    (Grad.KernelPullback.Domain.domainPullback_trans Value domain measurable first second
      firstInvariant secondInvariant compositionInvariant)

theorem pullback_covector_commute (rank : ℕ) (spatial covector : Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : Grad.KernelPullback.Domain.Invariant domain spatial)
    (fields : Tensor rank (DomainL2 Value domain)) :
    entrywisePullback Value domain measurable rank spatial invariant
        (covectorAction (DomainL2 Value domain) rank covector fields) =
      covectorAction (DomainL2 Value domain) rank covector
        (entrywisePullback Value domain measurable rank spatial invariant fields) := by
  apply PiLp.ext
  intro output
  exact covectorAction_map (DomainL2 Value domain)
    (Grad.KernelPullback.Domain.domainPullbackCLM Value domain measurable spatial invariant)
      rank covector fields output

def tensorLift (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : Grad.KernelPullback.Domain.Invariant domain orthogonal) :
    Tensor rank (DomainL2 Value domain) ≃ₗᵢ[ℂ] Tensor rank (DomainL2 Value domain) :=
  (entrywisePullback Value domain measurable rank orthogonal invariant).trans
    (covectorEquivalence (DomainL2 Value domain) rank orthogonal)

theorem tensorLift_apply (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : Grad.KernelPullback.Domain.Invariant domain orthogonal)
    (fields : Tensor rank (DomainL2 Value domain)) :
    tensorLift Value domain measurable rank orthogonal invariant fields =
      covectorAction (DomainL2 Value domain) rank orthogonal
        (entrywisePullback Value domain measurable rank orthogonal invariant fields) := rfl

theorem tensorLift_norm (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : Grad.KernelPullback.Domain.Invariant domain orthogonal)
    (fields : Tensor rank (DomainL2 Value domain)) :
    ‖tensorLift Value domain measurable rank orthogonal invariant fields‖ = ‖fields‖ :=
  (tensorLift Value domain measurable rank orthogonal invariant).norm_map fields

theorem tensorLift_trans (rank : ℕ) (first second : Spatial ≃ₗᵢ[ℝ] Spatial)
    (firstInvariant : Grad.KernelPullback.Domain.Invariant domain first)
    (secondInvariant : Grad.KernelPullback.Domain.Invariant domain second)
    (compositionInvariant : Grad.KernelPullback.Domain.Invariant domain (first.trans second))
    (fields : Tensor rank (DomainL2 Value domain)) :
    tensorLift Value domain measurable rank (first.trans second) compositionInvariant fields =
      tensorLift Value domain measurable rank first firstInvariant
        (tensorLift Value domain measurable rank second secondInvariant fields) := by
  rw [tensorLift_apply, tensorLift_apply, tensorLift_apply, entrywisePullback_trans,
    covectorAction_trans, pullback_covector_commute]

theorem tensorLift_ae (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : Grad.KernelPullback.Domain.Invariant domain orthogonal)
    (fields : Tensor rank (DomainL2 Value domain)) :
    ∀ᵐ point ∂volume.restrict domain, ∀ output : Fin rank → Fin 2,
      tensorLift Value domain measurable rank orthogonal invariant fields output point =
        ∑ input : Fin rank → Fin 2,
          (TensorCoefficients.tensorCoefficient rank (OrthogonalCoefficients.coefficient orthogonal)
            output input : ℂ) • fields input (orthogonal point) := by
  filter_upwards [covectorAction_lp_ae Value (volume.restrict domain) rank orthogonal
      (entrywisePullback Value domain measurable rank orthogonal invariant fields),
    entrywisePullback_ae Value domain measurable rank orthogonal invariant fields]
    with point acted pulled
  intro output
  change covectorAction (DomainL2 Value domain) rank orthogonal
    (entrywisePullback Value domain measurable rank orthogonal invariant fields) output point = _
  rw [acted output]
  change (∑ input, (TensorCoefficients.tensorCoefficient rank
    (OrthogonalCoefficients.coefficient orthogonal) output input : ℂ) •
      entrywisePullback Value domain measurable rank orthogonal invariant fields input point) = _
  exact Finset.sum_congr rfl (fun input _membership => congrArg
    (fun value : Value => (TensorCoefficients.tensorCoefficient rank
      (OrthogonalCoefficients.coefficient orthogonal) output input : ℂ) • value) (pulled input))

end Grad.TensorAction.Generic
