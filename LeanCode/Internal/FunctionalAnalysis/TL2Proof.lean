import TL2Interface

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Grad.TensorLpExchange.Generic

universe indexUniverse valueUniverse pointUniverse

variable (Index : Type indexUniverse) [Fintype Index]
variable (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
variable {Point : Type pointUniverse} [MeasurableSpace Point] (measure : Measure Point)

theorem singleton_expansion [DecidableEq Index] (values : Index → Value) :
    (WithLp.toLp 2 values : Values Index Value) =
      ∑ index : Index, PiLp.single 2 index (values index) := by
  apply PiLp.ext
  intro output
  change values output =
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Index => Value) output)
      (∑ index : Index, PiLp.single 2 index (values index))
  rw [map_sum]
  symm
  calc
    _ = (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Index => Value) output)
        (PiLp.single 2 output (values output)) := by
      apply Fintype.sum_eq_single output
      intro index different
      exact PiLp.single_eq_of_ne' (β := fun _ : Index => Value) 2 different (values index)
    _ = values output := PiLp.single_eq_same (β := fun _ : Index => Value) 2 output _

theorem assembled_aestronglyMeasurable (representatives : Index → Point → Value)
    (membership : ∀ index, MemLp (representatives index) 2 measure) :
    AEStronglyMeasurable (assemble Index Value representatives) measure := by
  classical
  have expansion : assemble Index Value representatives =
      (fun point => ∑ index : Index,
        (PiLp.single 2 index (representatives index point) : Values Index Value)) := by
    funext point
    exact singleton_expansion Index Value (fun index => representatives index point)
  rw [expansion]
  apply Finset.aestronglyMeasurable_fun_sum
  intro index _membership
  exact (isometry_iff_dist_eq.mpr
    (PiLp.dist_single_same 2 (fun _ : Index => Value) index)).continuous.comp_aestronglyMeasurable
      (membership index).aestronglyMeasurable

omit [InnerProductSpace ℂ Value] in
theorem assembled_integrable_sq (representatives : Index → Point → Value)
    (membership : ∀ index, MemLp (representatives index) 2 measure) :
    Integrable (fun point => ‖assemble Index Value representatives point‖ ^ 2) measure := by
  simpa only [assemble, PiLp.norm_sq_eq_of_L2, PiLp.toLp_apply] using
    (integrable_finsetSum Finset.univ (fun index _ => (membership index).norm.integrable_sq))

theorem assembly : AssemblyGoal Index Value measure := by
  intro representatives membership
  exact (memLp_two_iff_integrable_sq_norm
    (assembled_aestronglyMeasurable Index Value measure representatives membership)).mpr
      (assembled_integrable_sq Index Value measure representatives membership)

omit [NormedAddCommGroup Value] [InnerProductSpace ℂ Value] in
theorem independence : IndependenceGoal Index Value measure := by
  intro first second agreement
  have simultaneous := ae_all_iff.mpr agreement
  filter_upwards [simultaneous] with point equalities
  exact PiLp.ext (fun index => equalities index)

theorem assembled_toLp_independent (first second : Index → Point → Value)
    (firstMembership : ∀ index, MemLp (first index) 2 measure)
    (secondMembership : ∀ index, MemLp (second index) 2 measure)
    (agreement : ∀ index, first index =ᵐ[measure] second index) :
    (assembly Index Value measure first firstMembership).toLp (assemble Index Value first) =
      (assembly Index Value measure second secondMembership).toLp (assemble Index Value second) :=
  MemLp.toLp_congr _ _ (independence Index Value measure first second agreement)

theorem lp_norm_sq (field : Lp Value 2 measure) :
    ‖field‖ ^ 2 = ∫ point, ‖field point‖ ^ 2 ∂measure := by
  let := InnerProductSpace.rclikeToReal ℂ Value
  calc
    ‖field‖ ^ 2 = inner ℝ field field := (real_inner_self_eq_norm_sq field).symm
    _ = ∫ point, inner ℝ (field point) (field point) ∂measure :=
      L2.inner_def (𝕜 := ℝ) field field
    _ = ∫ point, ‖field point‖ ^ 2 ∂measure := by simp only [real_inner_self_eq_norm_sq]

theorem source_norm_sq (field : Fields Index Value measure) :
    ‖field‖ ^ 2 = ∑ index : Index, ∫ point, ‖field index point‖ ^ 2 ∂measure := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl (fun index _ => lp_norm_sq Value measure (field index))

theorem target_coordinate_memLp (field : ValueField Index Value measure) (index : Index) :
    MemLp (fun point => field point index) 2 measure :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Index => Value) index).comp_memLp field

theorem target_norm_sq (field : ValueField Index Value measure) :
    ‖field‖ ^ 2 = ∑ index : Index, ∫ point, ‖field point index‖ ^ 2 ∂measure := by
  rw [lp_norm_sq (Values Index Value) measure]
  simp_rw [PiLp.norm_sq_eq_of_L2]
  exact integral_finsetSum Finset.univ
    (fun index _ => (target_coordinate_memLp Index Value measure field index).norm.integrable_sq)

theorem squareSum : SquareSumGoal Index Value measure :=
  ⟨source_norm_sq Index Value measure, target_norm_sq Index Value measure⟩

def collect (field : Fields Index Value measure) : ValueField Index Value measure :=
  (assembly Index Value measure (fun index => field index)
    (fun index => Lp.memLp (field index))).toLp
      (assemble Index Value (fun index => field index))

theorem collect_ae (field : Fields Index Value measure) :
    (collect Index Value measure field : Point → Values Index Value) =ᵐ[measure]
      assemble Index Value (fun index => field index) :=
  (assembly Index Value measure (fun index => field index)
    (fun index => Lp.memLp (field index))).coeFn_toLp

theorem collect_all_coordinates_ae (field : Fields Index Value measure) :
    ∀ᵐ point ∂measure, ∀ index : Index,
      collect Index Value measure field point index = field index point := by
  filter_upwards [collect_ae Index Value measure field] with point equality
  intro index
  exact congrArg (fun value : Values Index Value => value index) equality

theorem representatives_toLp_eq_collect (field : Fields Index Value measure)
    (representatives : Index → Point → Value)
    (membership : ∀ index, MemLp (representatives index) 2 measure)
    (agreement : ∀ index, representatives index =ᵐ[measure] (field index : Point → Value)) :
    (assembly Index Value measure representatives membership).toLp
        (assemble Index Value representatives) = collect Index Value measure field :=
  assembled_toLp_independent Index Value measure representatives (fun index => field index)
    membership (fun index => Lp.memLp (field index)) agreement

theorem separate_ae (field : ValueField Index Value measure) :
    ∀ᵐ point ∂measure, ∀ index : Index,
      separate Index Value measure field index point = field point index := by
  apply ae_all_iff.mpr
  intro index
  exact (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Index => Value) index).coeFn_compLpL field

theorem separate_collect (field : Fields Index Value measure) :
    separate Index Value measure (collect Index Value measure field) = field := by
  apply PiLp.ext
  intro index
  apply Lp.ext
  filter_upwards [separate_ae Index Value measure (collect Index Value measure field),
    collect_all_coordinates_ae Index Value measure field] with point separated collected
  exact (separated index).trans (collected index)

theorem collect_separate (field : ValueField Index Value measure) :
    collect Index Value measure (separate Index Value measure field) = field := by
  apply Lp.ext
  filter_upwards [collect_ae Index Value measure (separate Index Value measure field),
    separate_ae Index Value measure field] with point collected separated
  exact collected.trans (PiLp.ext separated)

theorem separate_injective : Function.Injective (separate Index Value measure) :=
  Function.LeftInverse.injective (collect_separate Index Value measure)

theorem separate_add (first second : ValueField Index Value measure) :
    separate Index Value measure (first + second) =
      separate Index Value measure first + separate Index Value measure second := by
  apply PiLp.ext
  intro index
  exact ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Index => Value) index).compLpL 2 measure).map_add _ _

theorem separate_smul (scalar : ℂ) (field : ValueField Index Value measure) :
    separate Index Value measure (scalar • field) = scalar • separate Index Value measure field := by
  apply PiLp.ext
  intro index
  exact ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Index => Value) index).compLpL 2 measure).map_smul _ _

theorem collect_add (first second : Fields Index Value measure) :
    collect Index Value measure (first + second) =
      collect Index Value measure first + collect Index Value measure second := by
  apply separate_injective Index Value measure
  rw [separate_add, separate_collect, separate_collect, separate_collect]

theorem collect_smul (scalar : ℂ) (field : Fields Index Value measure) :
    collect Index Value measure (scalar • field) = scalar • collect Index Value measure field := by
  apply separate_injective Index Value measure
  rw [separate_smul, separate_collect, separate_collect]

theorem collect_norm_sq (field : Fields Index Value measure) :
    ‖collect Index Value measure field‖ ^ 2 = ‖field‖ ^ 2 := by
  rw [target_norm_sq, source_norm_sq]
  apply Finset.sum_congr rfl
  intro index _membership
  apply integral_congr_ae
  filter_upwards [collect_all_coordinates_ae Index Value measure field] with point coordinates
  rw [coordinates index]

theorem collect_norm (field : Fields Index Value measure) :
    ‖collect Index Value measure field‖ = ‖field‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (collect_norm_sq Index Value measure field)

def exchange : Fields Index Value measure ≃ₗᵢ[ℂ] ValueField Index Value measure where
  toFun := collect Index Value measure
  invFun := separate Index Value measure
  left_inv := separate_collect Index Value measure
  right_inv := collect_separate Index Value measure
  map_add' := collect_add Index Value measure
  map_smul' := collect_smul Index Value measure
  norm_map' := collect_norm Index Value measure

theorem exchange_apply (field : Fields Index Value measure) :
    exchange Index Value measure field = collect Index Value measure field := rfl

theorem exchange_symm_apply (field : ValueField Index Value measure) :
    (exchange Index Value measure).symm field = separate Index Value measure field := rfl

theorem exchangeGoal : ExchangeGoal Index Value measure :=
  ⟨exchange Index Value measure, collect_all_coordinates_ae Index Value measure,
    separate_ae Index Value measure, exchange_symm_apply Index Value measure⟩

theorem block : BlockGoal Index Value measure :=
  ⟨assembly Index Value measure, independence Index Value measure,
    squareSum Index Value measure, exchangeGoal Index Value measure⟩

open Grad.PDEBootstrap (Spatial)

def orderedExchange (dimension rank : ℕ) (domain : Set Spatial) :
    Grad.GenericCarriers.OrderedFields dimension rank domain ≃ₗᵢ[ℂ]
      Grad.GenericCarriers.OrderedValueField dimension rank domain :=
  exchange (Fin rank → Fin 2) (Grad.GenericCarriers.CellValues dimension) (volume.restrict domain)

theorem orderedExchange_ae (dimension rank : ℕ) (domain : Set Spatial)
    (field : Grad.GenericCarriers.OrderedFields dimension rank domain) :
    ∀ᵐ point ∂volume.restrict domain, ∀ word : Fin rank → Fin 2,
      orderedExchange dimension rank domain field point word = field word point :=
  collect_all_coordinates_ae _ _ _ field

theorem orderedExchange_symm_ae (dimension rank : ℕ) (domain : Set Spatial)
    (field : Grad.GenericCarriers.OrderedValueField dimension rank domain) :
    ∀ᵐ point ∂volume.restrict domain, ∀ word : Fin rank → Fin 2,
      (orderedExchange dimension rank domain).symm field word point = field point word :=
  separate_ae _ _ _ field

theorem orderedExchange_symm_coordinate (dimension rank : ℕ) (domain : Set Spatial)
    (field : Grad.GenericCarriers.OrderedValueField dimension rank domain)
    (word : Fin rank → Fin 2) :
    (orderedExchange dimension rank domain).symm field word =
      Grad.GenericCarriers.fieldTensorProjection dimension rank domain word field := rfl

theorem orderedExchange_projection (dimension rank : ℕ) (domain : Set Spatial)
    (field : Grad.GenericCarriers.OrderedFields dimension rank domain) (word : Fin rank → Fin 2) :
    Grad.GenericCarriers.fieldTensorProjection dimension rank domain word
        (orderedExchange dimension rank domain field) = field word :=
  congrArg (fun tensor : Grad.GenericCarriers.OrderedFields dimension rank domain => tensor word)
    ((orderedExchange dimension rank domain).symm_apply_apply field)

theorem ordered_source_norm_sq (dimension rank : ℕ) (domain : Set Spatial)
    (field : Grad.GenericCarriers.OrderedFields dimension rank domain) :
    ‖field‖ ^ 2 = ∑ word : Fin rank → Fin 2,
      ∫ point : Spatial, ‖field word point‖ ^ 2 ∂volume.restrict domain :=
  source_norm_sq _ _ _ field

theorem ordered_target_norm_sq (dimension rank : ℕ) (domain : Set Spatial)
    (field : Grad.GenericCarriers.OrderedValueField dimension rank domain) :
    ‖field‖ ^ 2 = ∑ word : Fin rank → Fin 2,
      ∫ point : Spatial, ‖field point word‖ ^ 2 ∂volume.restrict domain :=
  target_norm_sq _ _ _ field

theorem orderedExchange_norm_sq (dimension rank : ℕ) (domain : Set Spatial)
    (field : Grad.GenericCarriers.OrderedFields dimension rank domain) :
    ‖orderedExchange dimension rank domain field‖ ^ 2 = ∑ word : Fin rank → Fin 2,
      ∫ point : Spatial, ‖field word point‖ ^ 2 ∂volume.restrict domain := by
  rw [(orderedExchange dimension rank domain).norm_map]
  exact ordered_source_norm_sq dimension rank domain field

theorem canonical : CanonicalGoal := by
  intro dimension rank domain
  exact ⟨orderedExchange dimension rank domain, orderedExchange_ae dimension rank domain,
    orderedExchange_symm_ae dimension rank domain, ordered_source_norm_sq dimension rank domain,
    orderedExchange_norm_sq dimension rank domain⟩

end Grad.TensorLpExchange.Generic
