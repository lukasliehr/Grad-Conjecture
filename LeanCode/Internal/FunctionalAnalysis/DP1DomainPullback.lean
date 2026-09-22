import DP1MeasurePreserving

noncomputable section

open MeasureTheory Grad.PDEBootstrap

namespace Grad.KernelPullback.Domain

def domainPullback (Value : Type*) [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (domain : Set Spatial) (measurable : MeasurableSet domain)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (invariant : Invariant domain orthogonal) :
    DomainL2 Value domain ≃ₗᵢ[ℂ] DomainL2 Value domain where
  toFun := Lp.compMeasurePreservingₗᵢ ℂ orthogonal
    (domainMeasurePreserving domain measurable orthogonal invariant)
  map_add' := (Lp.compMeasurePreservingₗᵢ ℂ orthogonal
    (domainMeasurePreserving domain measurable orthogonal invariant)).map_add
  map_smul' := (Lp.compMeasurePreservingₗᵢ ℂ orthogonal
    (domainMeasurePreserving domain measurable orthogonal invariant)).map_smul
  norm_map' := (Lp.compMeasurePreservingₗᵢ ℂ orthogonal
    (domainMeasurePreserving domain measurable orthogonal invariant)).norm_map
  invFun := Lp.compMeasurePreserving orthogonal.symm
    (domainMeasurePreserving domain measurable orthogonal.symm
      (invariant_symm domain orthogonal invariant))
  left_inv := by
    intro field
    change Lp.compMeasurePreserving orthogonal.symm
      (domainMeasurePreserving domain measurable orthogonal.symm
        (invariant_symm domain orthogonal invariant))
      (Lp.compMeasurePreserving orthogonal
        (domainMeasurePreserving domain measurable orthogonal invariant) field) = field
    rw [← Lp.compMeasurePreserving_comp_apply]
    have composition : (⇑orthogonal ∘ ⇑orthogonal.symm : Spatial → Spatial) = id :=
      funext orthogonal.apply_symm_apply
    simpa only [composition] using Lp.compMeasurePreserving_id_apply field
  right_inv := by
    intro field
    change Lp.compMeasurePreserving orthogonal
      (domainMeasurePreserving domain measurable orthogonal invariant)
      (Lp.compMeasurePreserving orthogonal.symm
        (domainMeasurePreserving domain measurable orthogonal.symm
          (invariant_symm domain orthogonal invariant)) field) = field
    rw [← Lp.compMeasurePreserving_comp_apply]
    have composition : (⇑orthogonal.symm ∘ ⇑orthogonal : Spatial → Spatial) = id :=
      funext orthogonal.symm_apply_apply
    simpa only [composition] using Lp.compMeasurePreserving_id_apply field

variable (Value : Type*) [NormedAddCommGroup Value] [NormedSpace ℂ Value]

theorem domainPullback_apply (domain : Set Spatial) (measurable : MeasurableSet domain)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (invariant : Invariant domain orthogonal)
    (field : DomainL2 Value domain) :
    domainPullback Value domain measurable orthogonal invariant field =
      Lp.compMeasurePreserving orthogonal
        (domainMeasurePreserving domain measurable orthogonal invariant) field := rfl

theorem domainPullback_ae (domain : Set Spatial) (measurable : MeasurableSet domain)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (invariant : Invariant domain orthogonal)
    (field : DomainL2 Value domain) :
    (domainPullback Value domain measurable orthogonal invariant field : Spatial → Value) =ᵐ[
      (volume : Measure Spatial).restrict domain] fun point => field (orthogonal point) :=
  Lp.coeFn_compMeasurePreserving field
    (domainMeasurePreserving domain measurable orthogonal invariant)

theorem domainPullback_symm_ae (domain : Set Spatial) (measurable : MeasurableSet domain)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (invariant : Invariant domain orthogonal)
    (field : DomainL2 Value domain) :
    ((domainPullback Value domain measurable orthogonal invariant).symm field : Spatial → Value) =ᵐ[
      (volume : Measure Spatial).restrict domain] fun point => field (orthogonal.symm point) :=
  Lp.coeFn_compMeasurePreserving field
    (domainMeasurePreserving domain measurable orthogonal.symm
      (invariant_symm domain orthogonal invariant))

theorem domainPullback_symm (domain : Set Spatial) (measurable : MeasurableSet domain)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (invariant : Invariant domain orthogonal)
    (inverseInvariant : Invariant domain orthogonal.symm) :
    (domainPullback Value domain measurable orthogonal invariant).symm =
      domainPullback Value domain measurable orthogonal.symm inverseInvariant := by
  apply LinearIsometryEquiv.ext
  intro field
  rfl

theorem domainPullback_refl (domain : Set Spatial) (measurable : MeasurableSet domain)
    (invariant : Invariant domain (LinearIsometryEquiv.refl ℝ Spatial)) :
    domainPullback Value domain measurable (LinearIsometryEquiv.refl ℝ Spatial) invariant =
      LinearIsometryEquiv.refl ℂ (DomainL2 Value domain) := by
  apply LinearIsometryEquiv.ext
  intro field
  exact Lp.compMeasurePreserving_id_apply field

theorem domainPullback_trans (domain : Set Spatial) (measurable : MeasurableSet domain)
    (first second : Spatial ≃ₗᵢ[ℝ] Spatial)
    (firstInvariant : Invariant domain first) (secondInvariant : Invariant domain second)
    (compositionInvariant : Invariant domain (first.trans second)) :
    domainPullback Value domain measurable (first.trans second) compositionInvariant =
      (domainPullback Value domain measurable second secondInvariant).trans
        (domainPullback Value domain measurable first firstInvariant) := by
  apply LinearIsometryEquiv.ext
  intro field
  exact Lp.compMeasurePreserving_comp_apply field
    (domainMeasurePreserving domain measurable second secondInvariant)
    (domainMeasurePreserving domain measurable first firstInvariant)

theorem domainPullback_norm (domain : Set Spatial) (measurable : MeasurableSet domain)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (invariant : Invariant domain orthogonal)
    (field : DomainL2 Value domain) :
    ‖domainPullback Value domain measurable orthogonal invariant field‖ = ‖field‖ :=
  (domainPullback Value domain measurable orthogonal invariant).norm_map field

def domainPullbackCLM (domain : Set Spatial) (measurable : MeasurableSet domain)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (invariant : Invariant domain orthogonal) :
    DomainL2 Value domain →L[ℂ] DomainL2 Value domain :=
  (domainPullback Value domain measurable orthogonal invariant).toLinearIsometry.toContinuousLinearMap

theorem domainPullbackCLM_norm_le (domain : Set Spatial) (measurable : MeasurableSet domain)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (invariant : Invariant domain orthogonal) :
    ‖domainPullbackCLM Value domain measurable orthogonal invariant‖ ≤ 1 :=
  (domainPullback Value domain measurable orthogonal invariant).toLinearIsometry.norm_toContinuousLinearMap_le

theorem domainPullbackCLM_norm_eq_one (domain : Set Spatial) (measurable : MeasurableSet domain)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (invariant : Invariant domain orthogonal)
    (nontrivial : Nontrivial (DomainL2 Value domain)) :
    ‖domainPullbackCLM Value domain measurable orthogonal invariant‖ = 1 := by
  let := nontrivial
  exact (domainPullback Value domain measurable orthogonal invariant).toLinearIsometry.norm_toContinuousLinearMap

theorem domainPullbackCLM_norm_eq_zero (domain : Set Spatial) (measurable : MeasurableSet domain)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (invariant : Invariant domain orthogonal)
    (subsingleton : Subsingleton (DomainL2 Value domain)) :
    ‖domainPullbackCLM Value domain measurable orthogonal invariant‖ = 0 := by
  let := subsingleton
  exact ContinuousLinearMap.opNorm_subsingleton
    (domainPullbackCLM Value domain measurable orthogonal invariant)

def volumeMeasureTransport
    {source target : @Measure Spatial (inferInstance : MeasureSpace Spatial).toMeasurableSpace}
    (equality : source = target) :
    Lp (m := (inferInstance : MeasureSpace Spatial).toMeasurableSpace) Value 2 source ≃ₗᵢ[ℂ]
      Lp (m := (inferInstance : MeasureSpace Spatial).toMeasurableSpace) Value 2 target :=
  measureTransport Value equality

theorem measureTransport_compMeasurePreserving
    {source target : @Measure Spatial (inferInstance : MeasureSpace Spatial).toMeasurableSpace}
    (equality : source = target) (mapping : Spatial → Spatial)
    (sourcePreserving : MeasurePreserving mapping source source)
    (targetPreserving : MeasurePreserving mapping target target) (field : Lp Value 2 source) :
    volumeMeasureTransport Value equality (Lp.compMeasurePreserving mapping sourcePreserving field) =
      Lp.compMeasurePreserving mapping targetPreserving (volumeMeasureTransport Value equality field) := by
  subst target
  rfl

theorem univToVolume_eq_volumeMeasureTransport :
    univToVolume Value =
      volumeMeasureTransport Value (source := (volume : Measure Spatial).restrict Set.univ)
        (target := volume) Measure.restrict_univ := rfl

set_option maxHeartbeats 2000000 in
theorem univToVolume_apply (field : DomainL2 Value Set.univ) :
    univToVolume Value field =
      volumeMeasureTransport Value (source := (volume : Measure Spatial).restrict Set.univ)
        (target := volume) Measure.restrict_univ field :=
  congrArg (fun transport : DomainL2 Value Set.univ ≃ₗᵢ[ℂ] Lp Value 2 (volume : Measure Spatial) =>
    transport field) (univToVolume_eq_volumeMeasureTransport Value)

set_option maxHeartbeats 2000000 in
theorem domainPullback_univ_apply (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : Invariant Set.univ orthogonal) (field : DomainL2 Value Set.univ) :
    univToVolume Value (domainPullback Value Set.univ MeasurableSet.univ orthogonal invariant field) =
      Lp.compMeasurePreserving orthogonal orthogonal.measurePreserving (univToVolume Value field) := by
  calc
    _ = volumeMeasureTransport Value Measure.restrict_univ
        (domainPullback Value Set.univ MeasurableSet.univ orthogonal invariant field) :=
      univToVolume_apply Value _
    _ = volumeMeasureTransport Value Measure.restrict_univ
        (Lp.compMeasurePreserving orthogonal
          (domainMeasurePreserving Set.univ MeasurableSet.univ orthogonal invariant) field) :=
      congrArg (volumeMeasureTransport Value Measure.restrict_univ)
        (domainPullback_apply Value Set.univ MeasurableSet.univ orthogonal invariant field)
    _ = Lp.compMeasurePreserving orthogonal orthogonal.measurePreserving
        (volumeMeasureTransport Value Measure.restrict_univ field) :=
      measureTransport_compMeasurePreserving Value Measure.restrict_univ orthogonal
        (domainMeasurePreserving Set.univ MeasurableSet.univ orthogonal invariant)
        orthogonal.measurePreserving field
    _ = _ := congrArg (Lp.compMeasurePreserving orthogonal orthogonal.measurePreserving)
      (univToVolume_apply Value field).symm

set_option maxHeartbeats 2000000 in
theorem domainPullback_laws : PullbackLaws Value (domainPullback Value) where
  measure_preserving := domainMeasurePreserving
  invariant_refl := invariant_refl
  invariant_symm := invariant_symm
  invariant_trans := invariant_trans
  apply_ae := domainPullback_ae Value
  symm_apply_ae := domainPullback_symm_ae Value
  symm_eq := domainPullback_symm Value
  refl_eq := domainPullback_refl Value
  trans_eq := domainPullback_trans Value
  norm_map := domainPullback_norm Value
  opNorm_le := domainPullbackCLM_norm_le Value
  opNorm_eq_one := domainPullbackCLM_norm_eq_one Value
  opNorm_eq_zero := domainPullbackCLM_norm_eq_zero Value
  univ_apply := domainPullback_univ_apply Value

theorem constructor : constructorGoal Value :=
  ⟨domainPullback Value, domainPullback_laws Value⟩

end Grad.KernelPullback.Domain
