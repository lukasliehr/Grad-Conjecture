import T1Translation

noncomputable section

open MeasureTheory Grad.PDEBootstrap

universe valueUniverse

namespace Grad.SpatialTranslation

variable (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]

theorem identity_mpr_heq {Source Target : Sort valueUniverse}
    (equality : Source = Target) (value : Target) : HEq (id (equality.mpr value)) value := by
  cases equality
  exact HEq.rfl

def measureIdentityEquiv {source target : Measure Spatial} (equality : source = target) :
    Lp Value 2 source ≃ₗᵢ[ℂ] Lp Value 2 target :=
  equality ▸ LinearIsometryEquiv.refl ℂ (Lp Value 2 source)

theorem measureIdentityEquiv_heq {source target : Measure Spatial} (equality : source = target) :
    HEq (measureIdentityEquiv Value equality) (LinearIsometryEquiv.refl ℂ (Lp Value 2 target)) := by
  subst target
  exact HEq.rfl

def PreservesRepresentatives {source target : Measure Spatial}
    (equivalence : Lp Value 2 source ≃ₗᵢ[ℂ] Lp Value 2 target) : Prop :=
  ∀ field : Lp Value 2 source, equivalence field =ᵐ[target] field

theorem measureIdentityEquiv_ae {source target : Measure Spatial} (equality : source = target) :
    PreservesRepresentatives Value (measureIdentityEquiv Value equality) := by
  subst target
  exact fun _ => Filter.EventuallyEq.rfl

theorem canonicalToVolume_heq :
    HEq (canonicalToVolume Value) (LinearIsometryEquiv.refl ℂ (Lp Value 2 (volume : Measure Spatial))) := by
  unfold canonicalToVolume
  exact identity_mpr_heq _ _

theorem canonicalToVolume_eq : canonicalToVolume Value =
    measureIdentityEquiv Value (Measure.restrict_univ (μ := (volume : Measure Spatial))) :=
  eq_of_heq ((canonicalToVolume_heq Value).trans (measureIdentityEquiv_heq Value _).symm)

theorem canonicalToVolume_norm (field : PlaneL2 Value) : ‖canonicalToVolume Value field‖ = ‖field‖ := by
  generalize equality : canonicalToVolume Value = equivalence
  exact equivalence.norm_map field

theorem canonicalToVolume_ae : PreservesRepresentatives Value (canonicalToVolume Value) := by
  rw [canonicalToVolume_eq]
  exact measureIdentityEquiv_ae Value _

def IntertwinesTranslations
    (equivalence : PlaneL2 Value ≃ₗᵢ[ℂ] Lp Value 2 (volume : Measure Spatial)) : Prop :=
  ∀ (offset : Spatial) (field : PlaneL2 Value),
    equivalence (translation Value offset field) =
      Lp.compMeasurePreserving (shiftFamily offset) (shift_measurePreserving offset) (equivalence field)

theorem intertwinesTranslations_of_representatives
    (equivalence : PlaneL2 Value ≃ₗᵢ[ℂ] Lp Value 2 (volume : Measure Spatial))
    (representatives : PreservesRepresentatives Value equivalence) :
    IntertwinesTranslations Value equivalence := by
  intro offset field
  apply Lp.ext
  filter_upwards [representatives (translation Value offset field),
    translation_ae Value offset field,
    Lp.coeFn_compMeasurePreserving (equivalence field) (shift_measurePreserving offset),
    (shift_measurePreserving offset).quasiMeasurePreserving.ae_eq_comp
      (representatives field)] with point canonical shifted composed original
  exact canonical.trans (shifted.trans (original.symm.trans composed.symm))

theorem canonicalToVolume_translation : IntertwinesTranslations Value (canonicalToVolume Value) :=
  intertwinesTranslations_of_representatives Value _ (canonicalToVolume_ae Value)

theorem canonical_properties
    (equivalence : type_of% (canonicalToVolume Value))
    (representatives : PreservesRepresentatives Value equivalence) :
    (∀ field : Grad.GenericCarriers.DomainL2 Value Set.univ,
      ‖equivalence field‖ = ‖field‖ ∧ equivalence field =ᵐ[(volume : Measure Spatial)] field) ∧
    (∀ (offset : Spatial) (field : Grad.GenericCarriers.DomainL2 Value Set.univ),
      equivalence (translation Value offset field) =
        Lp.compMeasurePreserving (shiftFamily offset) (shift_measurePreserving offset)
          (equivalence field)) :=
  ⟨fun field => ⟨equivalence.norm_map field, representatives field⟩,
    intertwinesTranslations_of_representatives Value equivalence representatives⟩

def univToVolume : PlaneL2 Value →ₗᵢ[ℂ] Lp Value 2 (volume : Measure Spatial) :=
  Lp.compMeasurePreservingₗᵢ ℂ id
    (by simpa only [Measure.restrict_univ] using MeasurePreserving.id (volume : Measure Spatial))

theorem univToVolume_ae (field : PlaneL2 Value) : univToVolume Value field =ᵐ[volume] field :=
  Lp.coeFn_compMeasurePreserving field _

def AgreesWithVolumeMap (equivalence : type_of% (canonicalToVolume Value)) : Prop :=
  ∀ field : PlaneL2 Value, equivalence field = univToVolume Value field

theorem agreesWithVolumeMap_of_representatives (equivalence : type_of% (canonicalToVolume Value))
    (representatives : PreservesRepresentatives Value equivalence) :
    AgreesWithVolumeMap Value equivalence := by
  intro field
  exact Lp.ext ((representatives field).trans (univToVolume_ae Value field).symm)

theorem canonicalToVolume_apply_eq : AgreesWithVolumeMap Value (canonicalToVolume Value) :=
  agreesWithVolumeMap_of_representatives Value _ (canonicalToVolume_ae Value)

theorem univToVolume_translation (offset : Spatial) (field : PlaneL2 Value) :
    univToVolume Value (translation Value offset field) =
      Lp.compMeasurePreserving (shiftFamily offset) (shift_measurePreserving offset)
        (univToVolume Value field) := by
  apply Lp.ext
  filter_upwards [univToVolume_ae Value (translation Value offset field),
    translation_ae Value offset field,
    Lp.coeFn_compMeasurePreserving (univToVolume Value field) (shift_measurePreserving offset),
    (shift_measurePreserving offset).quasiMeasurePreserving.ae_eq_comp
      (univToVolume_ae Value field)] with point canonical shifted composed original
  exact canonical.trans (shifted.trans (original.symm.trans composed.symm))

theorem canonical : CanonicalGoal.{valueUniverse} := by
  intro Value normed inner
  have representatives := canonicalToVolume_ae Value
  generalize equality : canonicalToVolume Value = equivalence at representatives ⊢
  clear equality
  as_aux_lemma => exact canonical_properties Value equivalence representatives

end Grad.SpatialTranslation
