import GC1Interface

noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

namespace Grad.GenericCarriers

open Grad.PDEBootstrap (Spatial)

universe valueUniverse indexUniverse

def singleCellSpan (Value : Type valueUniverse) [NormedAddCommGroup Value] [NormedSpace ℂ Value] :
    Submodule ℂ (Cells Value) :=
  Submodule.span ℂ (⋃ cell : ℤ, Set.range (cellSingle Value cell))

theorem single_mem_singleCellSpan (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (cell : ℤ) (value : Value) :
    cellSingle Value cell value ∈ singleCellSpan Value :=
  Submodule.subset_span (Set.mem_iUnion.mpr ⟨cell, ⟨value, rfl⟩⟩)

theorem singleCellSpan_closure (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] : (singleCellSpan Value).topologicalClosure = ⊤ := by
  apply top_unique
  intro cells _
  have convergence : HasSum (fun cell : ℤ => cellSingle Value cell (cells cell)) cells :=
    lp.hasSum_single (by norm_num) cells
  apply (singleCellSpan Value).isClosed_topologicalClosure.mem_of_tendsto convergence
  exact Filter.Eventually.of_forall (fun support =>
    (singleCellSpan Value).topologicalClosure.sum_mem (fun cell _ =>
      (singleCellSpan Value).le_topologicalClosure (single_mem_singleCellSpan Value cell (cells cell))))

theorem singleCellSpan_dense (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] : Dense (singleCellSpan Value : Set (Cells Value)) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr (singleCellSpan_closure Value)

theorem singleCellSpan_separable (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] [SeparableSpace Value] :
    TopologicalSpace.IsSeparable (singleCellSpan Value : Set (Cells Value)) :=
  TopologicalSpace.IsSeparable.span (R := ℂ)
    (TopologicalSpace.IsSeparable.iUnion (fun cell : ℤ =>
      isSeparable_range (cellSingle Value cell).continuous))

instance cellsSeparable (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] [SeparableSpace Value] : SeparableSpace (Cells Value) := by
  apply TopologicalSpace.isSeparable_univ_iff.mp
  have separableClosure := (singleCellSpan_separable Value).closure
  rw [← Submodule.topologicalClosure_coe, singleCellSpan_closure] at separableClosure
  exact separableClosure

instance cellsSecondCountable (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] [SeparableSpace Value] : SecondCountableTopology (Cells Value) :=
  UniformSpace.secondCountable_of_separable (Cells Value)

instance orderedCellValuesSeparable (dimension rank : ℕ) :
    SeparableSpace (OrderedCellValues dimension rank) := inferInstance

instance lpTwoSecondCountable (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [SeparableSpace Value] (measure : Measure Spatial) [MeasureTheory.IsSeparable measure] :
    SecondCountableTopology (Lp Value 2 measure) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  exact Lp.SecondCountableTopology

theorem physicalProjection_apply (dimension : ℕ) (value : PhysicalValue dimension)
    (coordinate : Fin dimension) : physicalProjection dimension coordinate value = value coordinate := rfl

theorem physicalProjection_ofCoordinates (dimension : ℕ) (coordinates : Fin dimension → ℂ)
    (coordinate : Fin dimension) :
    physicalProjection dimension coordinate (physicalOfCoordinates dimension coordinates) =
      coordinates coordinate := rfl

theorem cellsOfCoordinates_apply {Value : Type valueUniverse} [NormedAddCommGroup Value]
    (coordinates : ℤ → Value) (membership : Memℓp coordinates 2) (cell : ℤ) :
    cellsOfCoordinates coordinates membership cell = coordinates cell := rfl

theorem cellProjection_apply {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (cells : Cells Value) (cell : ℤ) :
    cellProjection Value cell cells = cells cell := rfl

theorem cellSingle_apply {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (cell other : ℤ) (value : Value) :
    cellSingle Value cell value other = if other = cell then value else 0 := by
  change lp.single (E := fun _ : ℤ => Value) 2 cell value other = _
  rw [lp.single_apply]
  by_cases same : other = cell
  · subst other
    simp
  · rw [Pi.single_eq_of_ne same, if_neg same]

theorem tensorProjection_apply {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (rank : ℕ) (tensor : Tensor rank Value) (word : Fin rank → Fin 2) :
    tensorProjection Value rank word tensor = tensor word := rfl

theorem tensorProjection_ofCoordinates {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (rank : ℕ) (coordinates : (Fin rank → Fin 2) → Value)
    (word : Fin rank → Fin 2) :
    tensorProjection Value rank word (tensorOfCoordinates rank coordinates) = coordinates word := rfl

theorem graphProjection_apply {Index : Type indexUniverse} [Fintype Index]
    {Fiber : Index → Type valueUniverse} [∀ index, NormedAddCommGroup (Fiber index)]
    [∀ index, NormedSpace ℂ (Fiber index)] (graph : GraphTuple Index Fiber) (index : Index) :
    graphProjection Index Fiber index graph = graph index := rfl

theorem graphProjection_ofCoordinates {Index : Type indexUniverse} [Fintype Index]
    {Fiber : Index → Type valueUniverse} [∀ index, NormedAddCommGroup (Fiber index)]
    [∀ index, NormedSpace ℂ (Fiber index)] (coordinates : ∀ index, Fiber index) (index : Index) :
    graphProjection Index Fiber index (graphOfCoordinates coordinates) = coordinates index := rfl

theorem coordinate : CoordinateGoal.{valueUniverse, indexUniverse} :=
  ⟨physicalProjection_ofCoordinates, fun _ _ => cellsOfCoordinates_apply,
    fun _ _ _ => cellProjection_apply, fun _ _ _ => cellSingle_apply,
    fun _ _ _ => tensorProjection_ofCoordinates, fun _ _ _ _ _ => graphProjection_ofCoordinates⟩

theorem fieldOfRepresentative_ae {Value : Type valueUniverse} [NormedAddCommGroup Value]
    (domain : Set Spatial) (representative : Spatial → Value)
    (membership : MemLp representative 2 (volume.restrict domain)) :
    ∀ᵐ point ∂volume.restrict domain,
      fieldOfRepresentative domain representative membership point = representative point :=
  membership.coeFn_toLp

theorem fieldCellProjection_ae (dimension : ℕ) (domain : Set Spatial) (field : FieldL2 dimension domain) :
    ∀ᵐ point ∂volume.restrict domain, ∀ cell : ℤ,
      fieldCellProjection dimension domain cell field point = field point cell := by
  rw [ae_all_iff]
  intro cell
  exact (cellProjection (PhysicalValue dimension) cell).coeFn_compLpL field

theorem fieldTensorProjection_ae (dimension rank : ℕ) (domain : Set Spatial)
    (field : OrderedValueField dimension rank domain) :
    ∀ᵐ point ∂volume.restrict domain, ∀ word : Fin rank → Fin 2,
      fieldTensorProjection dimension rank domain word field point = field point word := by
  rw [ae_all_iff]
  intro word
  exact (tensorProjection (CellValues dimension) rank word).coeFn_compLpL field

theorem representative : RepresentativeGoal.{valueUniverse} :=
  ⟨fun _ _ => fieldOfRepresentative_ae, fieldCellProjection_ae, fieldTensorProjection_ae⟩

theorem physical_norm_sq (dimension : ℕ) (value : PhysicalValue dimension) :
    ‖value‖ ^ 2 = ∑ coordinate : Fin dimension, ‖value coordinate‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq value

theorem cells_norm_sq {Value : Type valueUniverse} [NormedAddCommGroup Value] (cells : Cells Value) :
    ‖cells‖ ^ 2 = ∑' cell : ℤ, ‖cells cell‖ ^ 2 :=
  Grad.TensorCellExchange.lp_norm_sq cells

theorem tensor_norm_sq {Value : Type valueUniverse} [NormedAddCommGroup Value]
    (rank : ℕ) (tensor : Tensor rank Value) :
    ‖tensor‖ ^ 2 = ∑ word : Fin rank → Fin 2, ‖tensor word‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ tensor

theorem graph_norm_sq {Index : Type indexUniverse} [Fintype Index]
    {Fiber : Index → Type valueUniverse} [∀ index, NormedAddCommGroup (Fiber index)]
    (graph : GraphTuple Index Fiber) : ‖graph‖ ^ 2 = ∑ index : Index, ‖graph index‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ graph

theorem lpTwo_norm_sq {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] (measure : Measure Spatial) (field : Lp Value 2 measure) :
    ‖field‖ ^ 2 = ∫ point : Spatial, ‖field point‖ ^ 2 ∂measure := by
  let := InnerProductSpace.rclikeToReal ℂ Value
  calc
    ‖field‖ ^ 2 = inner ℝ field field := (real_inner_self_eq_norm_sq field).symm
    _ = ∫ point : Spatial, inner ℝ (field point) (field point) ∂measure :=
      L2.inner_def (𝕜 := ℝ) field field
    _ = ∫ point : Spatial, ‖field point‖ ^ 2 ∂measure := by
      simp only [real_inner_self_eq_norm_sq]

theorem domainL2_norm_sq {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] (domain : Set Spatial) (field : DomainL2 Value domain) :
    ‖field‖ ^ 2 = ∫ point : Spatial, ‖field point‖ ^ 2 ∂volume.restrict domain :=
  lpTwo_norm_sq (volume.restrict domain) field

theorem orderedCellValues_norm_sq (dimension rank : ℕ) (tensor : OrderedCellValues dimension rank) :
    ‖tensor‖ ^ 2 = ∑ word : Fin rank → Fin 2, ∑' cell : ℤ, ‖tensor word cell‖ ^ 2 :=
  Grad.TensorCellExchange.source_norm_sq tensor

theorem orderedFields_norm_sq (dimension rank : ℕ) (domain : Set Spatial)
    (array : OrderedFields dimension rank domain) :
    ‖array‖ ^ 2 = ∑ word : Fin rank → Fin 2,
      ∫ point : Spatial, ‖array word point‖ ^ 2 ∂volume.restrict domain := by
  rw [tensor_norm_sq]
  exact Finset.sum_congr rfl (fun word _ => domainL2_norm_sq domain (array word))

theorem graphFields_norm_sq (dimension count : ℕ) (ranks : Fin count → ℕ) (domain : Set Spatial)
    (graph : GraphFields dimension count ranks domain) :
    ‖graph‖ ^ 2 = ∑ entry : Fin count, ∑ word : Fin (ranks entry) → Fin 2,
      ∫ point : Spatial, ‖graph entry word point‖ ^ 2 ∂volume.restrict domain := by
  rw [graph_norm_sq]
  exact Finset.sum_congr rfl (fun entry _ =>
    orderedFields_norm_sq dimension (ranks entry) domain (graph entry))

theorem normSquare : NormSquareGoal.{valueUniverse, indexUniverse} :=
  ⟨physical_norm_sq, fun _ _ => cells_norm_sq, fun _ _ => tensor_norm_sq,
    fun _ _ _ _ => graph_norm_sq, fun _ _ _ => domainL2_norm_sq,
    orderedCellValues_norm_sq, graphFields_norm_sq⟩

theorem physical_completeSeparable (dimension : ℕ) : CompleteSeparable (PhysicalValue dimension) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem cells_completeSeparable (dimension : ℕ) : CompleteSeparable (CellValues dimension) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem physicalTensor_completeSeparable (dimension rank : ℕ) :
    CompleteSeparable (Tensor rank (PhysicalValue dimension)) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem orderedCellValues_completeSeparable (dimension rank : ℕ) :
    CompleteSeparable (OrderedCellValues dimension rank) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem fieldL2_completeSeparable (dimension : ℕ) (domain : Set Spatial) :
    CompleteSeparable (FieldL2 dimension domain) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem orderedFields_completeSeparable (dimension rank : ℕ) (domain : Set Spatial) :
    CompleteSeparable (OrderedFields dimension rank domain) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem orderedValueField_completeSeparable (dimension rank : ℕ) (domain : Set Spatial) :
    CompleteSeparable (OrderedValueField dimension rank domain) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem graphFields_completeSeparable (dimension count : ℕ) (ranks : Fin count → ℕ)
    (domain : Set Spatial) : CompleteSeparable (GraphFields dimension count ranks domain) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem topology : TopologyGoal := by
  constructor
  · intro dimension
    exact ⟨physical_completeSeparable dimension, cells_completeSeparable dimension,
      fun rank => ⟨physicalTensor_completeSeparable dimension rank,
        orderedCellValues_completeSeparable dimension rank⟩⟩
  · intro dimension domain _openDomain
    exact ⟨fieldL2_completeSeparable dimension domain,
      fun rank => ⟨orderedFields_completeSeparable dimension rank domain,
        orderedValueField_completeSeparable dimension rank domain⟩,
      fun count ranks => graphFields_completeSeparable dimension count ranks domain⟩

theorem cellValues_three : CellValues 3 = Grad.PDEBootstrap.CellValues := rfl

theorem fieldL2_three : FieldL2 3 Set.univ = Grad.PDEBootstrap.FieldL2 :=
  congrArg (fun measure : Measure Spatial => (Lp (CellValues 3) 2 measure : Type))
    (Measure.restrict_univ (μ := volume))

theorem orderedCellValues_three (rank : ℕ) :
    OrderedCellValues 3 rank = Grad.TensorLpExchange.OrderedCellValues rank := rfl

theorem orderedFields_three (rank : ℕ) :
    OrderedFields 3 rank Set.univ = Grad.KernelArrays.OrderedFields rank :=
  congrArg (fun measure : Measure Spatial => PiLp 2
    (fun _ : Fin rank → Fin 2 => (Lp (CellValues 3) 2 measure : Type)))
    (Measure.restrict_univ (μ := volume))

theorem orderedValueField_three (rank : ℕ) :
    OrderedValueField 3 rank Set.univ = Grad.TensorLpExchange.OrderedValueField rank :=
  congrArg (fun measure : Measure Spatial => (Lp (OrderedCellValues 3 rank) 2 measure : Type))
    (Measure.restrict_univ (μ := volume))

theorem firstJet_three :
    GraphTuple (Fin 3) (fun _ => FieldL2 3 Set.univ) = Grad.PDEBootstrap.FirstJet :=
  congrArg (fun measure : Measure Spatial => PiLp 2
    (fun _ : Fin 3 => (Lp (CellValues 3) 2 measure : Type)))
    (Measure.restrict_univ (μ := volume))

theorem compatibility : CompatibilityGoal :=
  ⟨cellValues_three, fieldL2_three, orderedCellValues_three, orderedFields_three,
    orderedValueField_three, firstJet_three⟩

theorem block : BlockGoal.{valueUniverse, indexUniverse} :=
  ⟨coordinate, representative, normSquare, topology, compatibility⟩

end Grad.GenericCarriers
