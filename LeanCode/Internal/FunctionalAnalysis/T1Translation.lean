import T1Interface

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (DomainL2 CellValues PhysicalValue FieldL2)
open scoped Topology

universe valueUniverse otherUniverse

namespace Grad.SpatialTranslation

theorem ae_univ_iff {predicate : Spatial → Prop} :
    (∀ᵐ point ∂volume.restrict (Set.univ : Set Spatial), predicate point) ↔
      ∀ᵐ point ∂(volume : Measure Spatial), predicate point := by
  rw [Measure.restrict_univ]

variable (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]

theorem translation_ae (offset : Spatial) (field : PlaneL2 Value) :
    translation Value offset field =ᵐ[(volume : Measure Spatial)] fun point => field (point - offset) := by
  have equality : translation Value offset field =ᵐ[volume.restrict (Set.univ : Set Spatial)]
      fun point => field (point - offset) :=
    Lp.coeFn_compMeasurePreserving field (shift_univ_measurePreserving offset)
  exact ae_univ_iff.mp equality

theorem translation_zero (field : PlaneL2 Value) : translation Value 0 field = field := by
  change Lp.compMeasurePreserving (shiftFamily 0) (shift_univ_measurePreserving 0) field = field
  have zeroShift : (⇑(shiftFamily 0) : Spatial → Spatial) = id := by
    funext point
    exact sub_zero point
  simpa only [zeroShift] using Lp.compMeasurePreserving_id_apply field

theorem translation_add (first second : Spatial) (field : PlaneL2 Value) :
    translation Value first (translation Value second field) = translation Value (first + second) field := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ field) =
    Lp.compMeasurePreserving (shiftFamily (first + second)) (shift_univ_measurePreserving _) field
  rw [← Lp.compMeasurePreserving_comp_apply]
  have composition : (⇑(shiftFamily second) ∘ ⇑(shiftFamily first) : Spatial → Spatial) =
      shiftFamily (first + second) := by
    funext point
    change point - first - second = point - (first + second)
    abel
  simp only [composition]

theorem translation_inverse (offset : Spatial) (field : PlaneL2 Value) :
    translation Value (-offset) (translation Value offset field) = field ∧
      translation Value offset (translation Value (-offset) field) = field := by
  simp only [translation_add, neg_add_cancel, add_neg_cancel, translation_zero, and_self]

theorem translation_norm (offset : Spatial) (field : PlaneL2 Value) :
    ‖translation Value offset field‖ = ‖field‖ := (translation Value offset).norm_map field

def translationEquiv (offset : Spatial) : PlaneL2 Value ≃ₗᵢ[ℂ] PlaneL2 Value where
  toFun := translation Value offset
  map_add' := (translation Value offset).map_add
  map_smul' := (translation Value offset).map_smul
  norm_map' := (translation Value offset).norm_map
  invFun := translation Value (-offset)
  left_inv := fun field => (translation_inverse Value offset field).1
  right_inv := fun field => (translation_inverse Value offset field).2

theorem translationEquiv_apply (offset : Spatial) (field : PlaneL2 Value) :
    translationEquiv Value offset field = translation Value offset field := rfl

theorem translationEquiv_symm_apply (offset : Spatial) (field : PlaneL2 Value) :
    (translationEquiv Value offset).symm field = translation Value (-offset) field := rfl

theorem translation_joint_continuous :
    Continuous (fun pair : Spatial × PlaneL2 Value => translation Value pair.1 pair.2) := by
  let : (volume.restrict (Set.univ : Set Spatial)).InnerRegularCompactLTTop := by
    simpa only [Measure.restrict_univ] using
      (inferInstance : (volume : Measure Spatial).InnerRegularCompactLTTop)
  let : IsLocallyFiniteMeasure (volume.restrict (Set.univ : Set Spatial)) := by
    simpa only [Measure.restrict_univ] using
      (inferInstance : IsLocallyFiniteMeasure (volume : Measure Spatial))
  exact continuous_snd.compMeasurePreservingLp (shiftFamily.continuous.comp continuous_fst)
    (fun pair => shift_univ_measurePreserving pair.1) (by norm_num)

theorem translation_continuous (field : PlaneL2 Value) :
    Continuous (fun offset : Spatial => translation Value offset field) := by
  let : (volume.restrict (Set.univ : Set Spatial)).InnerRegularCompactLTTop := by
    simpa only [Measure.restrict_univ] using
      (inferInstance : (volume : Measure Spatial).InnerRegularCompactLTTop)
  let : IsLocallyFiniteMeasure (volume.restrict (Set.univ : Set Spatial)) := by
    simpa only [Measure.restrict_univ] using
      (inferInstance : IsLocallyFiniteMeasure (volume : Measure Spatial))
  exact continuous_const.compMeasurePreservingLp shiftFamily.continuous
    shift_univ_measurePreserving (by norm_num)

theorem translation_tendsto_zero (field : PlaneL2 Value) :
    Filter.Tendsto (fun offset : Spatial => translation Value offset field) (𝓝 0) (𝓝 field) := by
  simpa only [translation_zero] using (translation_continuous Value field).tendsto 0

theorem valueMap_ae (Other : Type otherUniverse) [NormedAddCommGroup Other] [InnerProductSpace ℂ Other]
    (mapping : Value →L[ℂ] Other) (field : PlaneL2 Value) :
    valueMap Value Other mapping field =ᵐ[(volume : Measure Spatial)] fun point => mapping (field point) := by
  have equality : valueMap Value Other mapping field =ᵐ[volume.restrict (Set.univ : Set Spatial)]
      fun point => mapping (field point) := mapping.coeFn_compLpL field
  exact ae_univ_iff.mp equality

theorem translation_natural (Other : Type otherUniverse) [NormedAddCommGroup Other]
    [InnerProductSpace ℂ Other] (mapping : Value →L[ℂ] Other) (offset : Spatial) (field : PlaneL2 Value) :
    valueMap Value Other mapping (translation Value offset field) =
      translation Other offset (valueMap Value Other mapping field) := by
  apply Lp.ext
  apply ae_univ_iff.mpr
  filter_upwards [valueMap_ae Value Other mapping (translation Value offset field),
    translation_ae Value offset field, translation_ae Other offset (valueMap Value Other mapping field),
    (shift_measurePreserving offset).quasiMeasurePreserving.ae_eq_comp
      (valueMap_ae Value Other mapping field)] with point mapped shifted target original
  exact mapped.trans ((congrArg mapping shifted).trans (original.symm.trans target.symm))

theorem isometry : IsometryGoal.{valueUniverse} := by
  intro Value normed inner
  exact ⟨translation_zero Value, translation_add Value, translation_inverse Value,
    translation_norm Value, translation_ae Value,
    fun offset => ⟨translationEquiv Value offset, translationEquiv_apply Value offset,
      translationEquiv_symm_apply Value offset⟩⟩

theorem continuity : ContinuityGoal.{valueUniverse} := by
  intro Value normed inner
  exact ⟨translation_joint_continuous Value, translation_continuous Value, translation_tendsto_zero Value⟩

theorem naturality : NaturalityGoal.{valueUniverse, otherUniverse} := by
  intro Value Other normed inner otherNormed otherInner
  exact translation_natural Value Other

theorem translation_coordinates (dimension : ℕ) (offset : Spatial) (field : FieldL2 dimension Set.univ) :
    ∀ᵐ point ∂(volume : Measure Spatial), ∀ (cell : ℤ) (physical : Fin dimension),
      translation (CellValues dimension) offset field point cell physical =
        field (point - offset) cell physical := by
  filter_upwards [translation_ae (CellValues dimension) offset field] with point equality cell physical
  exact congrArg (fun value : CellValues dimension => value cell physical) equality

theorem translation_cellProjection (dimension : ℕ) (offset : Spatial)
    (field : FieldL2 dimension Set.univ) (cell : ℤ) :
    Grad.GenericCarriers.fieldCellProjection dimension Set.univ cell
        (translation (CellValues dimension) offset field) =
      translation (PhysicalValue dimension) offset
        (Grad.GenericCarriers.fieldCellProjection dimension Set.univ cell field) :=
  translation_natural (CellValues dimension) (PhysicalValue dimension)
    (Grad.GenericCarriers.cellProjection (PhysicalValue dimension) cell) offset field

theorem cell : CellGoal := by
  intro dimension offset field
  exact ⟨translation_norm (CellValues dimension) offset field,
    translation_coordinates dimension offset field, translation_cellProjection dimension offset field⟩

end Grad.SpatialTranslation
