import P0910HigherJet

noncomputable section

open Filter Set
open scoped BigOperators ContDiff Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets
open Grad.DiskExtension.Seeley

def closedExteriorActiveRegion (index : ℕ) : Set SpatialCell :=
  {point | 1 ≤ ‖planarPart point‖ ∧
    node index * (‖planarPart point‖ - 1) ≤ 1}

def closedExteriorRegion : Set SpatialCell :=
  {point | 1 ≤ ‖planarPart point‖}

theorem closedExteriorActiveRegion_planarPart_ne_zero (index : ℕ)
    {point : SpatialCell} (membership : point ∈ closedExteriorActiveRegion index) :
    planarPart point ≠ 0 := by
  intro equality
  change 1 ≤ ‖planarPart point‖ ∧
    node index * (‖planarPart point‖ - 1) ≤ 1 at membership
  rw [equality, norm_zero] at membership
  linarith [membership.1]

theorem reflectedSpatialCell_mem_closedUnitCylinder_active (index : ℕ)
    {point : SpatialCell} (membership : point ∈ closedExteriorActiveRegion index) :
    reflectedSpatialCell index point ∈ closedUnitCylinder := by
  have outside : 1 ≤ ‖planarPart point‖ := membership.1
  have active : node index * (‖planarPart point‖ - 1) ≤ 1 := membership.2
  have scaleNonnegative : 0 ≤ node index * (‖planarPart point‖ - 1) :=
    mul_nonneg (node_positive index).le (sub_nonneg.mpr outside)
  have pointNormPositive : 0 < ‖planarPart point‖ :=
    lt_of_lt_of_le zero_lt_one outside
  change ‖planarPart (reflectedSpatialCell index point)‖ ≤ 1
  rw [reflectedSpatialCell_planarPart, reflectedPoint, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr active),
    abs_of_pos (inv_pos.mpr pointNormPositive)]
  field_simp
  linarith

theorem reflectedSpatialCell_contDiffOn_closedExteriorActiveRegion (index : ℕ) :
    ContDiffOn ℝ ∞ (reflectedSpatialCell index)
      (closedExteriorActiveRegion index) := by
  intro point membership
  exact (reflectedSpatialCell_contDiffAt index point
    (closedExteriorActiveRegion_planarPart_ne_zero index membership)).contDiffWithinAt

theorem exteriorScalar_contDiffOn_closedExteriorActiveRegion (index : ℕ) :
    ContDiffOn ℝ ∞ (exteriorScalar index) (closedExteriorActiveRegion index) := by
  intro point membership
  exact (exteriorScalar_contDiffAt index point
    (closedExteriorActiveRegion_planarPart_ne_zero index membership)).contDiffWithinAt

theorem diskCellLift_comp_reflectedSpatialCell_contDiffOn_active
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (index : ℕ) :
    ContDiffOn ℝ ∞ (diskCellLift field.value ∘ reflectedSpatialCell index)
      (closedExteriorActiveRegion index) := by
  exact (diskCellLift_contDiffOn_closed field).comp
    (reflectedSpatialCell_contDiffOn_closedExteriorActiveRegion index)
    (fun point membership =>
      reflectedSpatialCell_mem_closedUnitCylinder_active index membership)

theorem exteriorSummandCellLift_contDiffOn_active_closed
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (index : ℕ) :
    ContDiffOn ℝ ∞ (exteriorSummandCellLift field index)
      (closedExteriorActiveRegion index) := by
  rw [show exteriorSummandCellLift field index = fun point =>
      exteriorScalar index point •
        diskCellLift field.value (reflectedSpatialCell index point) by
    funext point
    exact exteriorSummandCellLift_formula field index point]
  exact (exteriorScalar_contDiffOn_closedExteriorActiveRegion index).smul
    (diskCellLift_comp_reflectedSpatialCell_contDiffOn_active field index)

theorem closedExteriorActiveRegion_eventually_eq_closedExteriorRegion
    (index : ℕ) (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    closedExteriorActiveRegion index =ᶠ[𝓝 point] closedExteriorRegion := by
  have scaleContinuous : ContinuousAt (fun candidate : SpatialCell =>
      node index * (‖planarPart candidate‖ - 1)) point :=
    ((continuous_norm.comp continuous_planarPart).continuousAt.sub
      continuousAt_const).const_mul _
  have scaleAt : node index * (‖planarPart point‖ - 1) < 1 := by
    rw [boundary, sub_self, mul_zero]
    norm_num
  filter_upwards [scaleContinuous.eventually (Iio_mem_nhds scaleAt)] with candidate
    candidateActive
  apply propext
  constructor
  · intro membership
    exact membership.1
  · intro membership
    exact ⟨membership, candidateActive.le⟩

theorem exteriorSummandCellLift_contDiffWithinAt_outer_boundary
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (index : ℕ)
    (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    ContDiffWithinAt ℝ ∞ (exteriorSummandCellLift field index)
      closedExteriorRegion point := by
  have activeMembership : point ∈ closedExteriorActiveRegion index := by
    exact ⟨boundary.symm.le, by rw [boundary, sub_self, mul_zero]; norm_num⟩
  exact (exteriorSummandCellLift_contDiffOn_active_closed field index point
    activeMembership).congr_set
      (closedExteriorActiveRegion_eventually_eq_closedExteriorRegion
        index point boundary)

def collarInterpolation (parameter : ℝ) (point : SpatialCell) : SpatialCell :=
  (1 - parameter) • normalizedSpatialCell point + parameter • point

@[simp] theorem collarInterpolation_one (point : SpatialCell) :
    collarInterpolation 1 point = point := by
  simp [collarInterpolation]

theorem collarInterpolation_neg_node (index : ℕ) (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    collarInterpolation (-node index) point = reflectedSpatialCell index point := by
  rw [reflectedSpatialCell_affine index point nonzero]
  unfold collarInterpolation
  module

theorem collarInterpolation_boundary (parameter : ℝ) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    collarInterpolation parameter point = point := by
  rw [collarInterpolation, normalizedSpatialCell_boundary point boundary]
  module

theorem collarInterpolation_contDiffAt (parameter : ℝ) (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    ContDiffAt ℝ ∞ (collarInterpolation parameter) point := by
  exact ((normalizedSpatialCell_contDiffAt point nonzero).const_smul
    (1 - parameter)).add (contDiffAt_id.const_smul parameter)

theorem iteratedFDeriv_collarInterpolation (order : ℕ) (parameter : ℝ)
    (point : SpatialCell) (nonzero : planarPart point ≠ 0) :
    iteratedFDeriv ℝ order (collarInterpolation parameter) point =
      (1 - parameter) • iteratedFDeriv ℝ order normalizedSpatialCell point +
        parameter • iteratedFDeriv ℝ order id point := by
  have normalizedSmooth : ContDiffAt ℝ order normalizedSpatialCell point :=
    (normalizedSpatialCell_contDiffAt point nonzero).of_le
      (WithTop.coe_le_coe.mpr
        (show (order : ℕ∞) ≤ ⊤ from le_top))
  have identitySmooth : ContDiffAt ℝ order (id : SpatialCell → SpatialCell) point :=
    contDiffAt_id
  change iteratedFDeriv ℝ order (fun candidate =>
      (1 - parameter) • normalizedSpatialCell candidate +
        parameter • id candidate) point = _
  calc
    _ = iteratedFDeriv ℝ order
          (fun candidate => (1 - parameter) • normalizedSpatialCell candidate) point +
        iteratedFDeriv ℝ order
          (fun candidate => parameter • id candidate) point := by
            exact iteratedFDeriv_add_apply
              (normalizedSmooth.const_smul (1 - parameter))
              (identitySmooth.const_smul parameter)
    _ = _ := by
      rw [iteratedFDeriv_const_smul_apply' normalizedSmooth,
        iteratedFDeriv_const_smul_apply' identitySmooth]

def vectorPolynomialEval {Value : Type*} [AddCommMonoid Value] [Module ℝ Value]
    (orders : Finset ℕ) (coefficientValue : ℕ → Value) (scale : ℝ) : Value :=
  ∑ order ∈ orders, scale ^ order • coefficientValue order

theorem iteratedFDeriv_collarInterpolation_vectorPolynomial (order : ℕ)
    (parameter : ℝ) (point : SpatialCell) (nonzero : planarPart point ≠ 0) :
    iteratedFDeriv ℝ order (collarInterpolation parameter) point =
      vectorPolynomialEval ({0, 1} : Finset ℕ)
        (fun degree => if degree = 0 then
          iteratedFDeriv ℝ order normalizedSpatialCell point
        else if degree = 1 then
          iteratedFDeriv ℝ order id point -
            iteratedFDeriv ℝ order normalizedSpatialCell point
        else 0) parameter := by
  rw [iteratedFDeriv_collarInterpolation order parameter point nonzero]
  simp [vectorPolynomialEval]
  module

theorem coefficient_vectorPolynomial_hasSum
    {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    [CompleteSpace Value] (orders : Finset ℕ) (coefficientValue : ℕ → Value) :
    HasSum (fun index => coefficient index •
        vectorPolynomialEval orders coefficientValue (-node index))
      (vectorPolynomialEval orders coefficientValue 1) := by
  classical
  induction orders using Finset.induction_on with
  | empty => simp [vectorPolynomialEval]
  | @insert order orders fresh inductionHypothesis =>
      have monomial : HasSum (fun index =>
          (coefficient index * (-node index) ^ order) • coefficientValue order)
          (coefficientValue order) := by
        have scalarMoment := (infinite_moment_hasSum order).smul_const
          (coefficientValue order)
        simpa only [node, one_smul] using scalarMoment
      simpa [vectorPolynomialEval, Finset.sum_insert fresh, smul_add, smul_smul]
        using monomial.add inductionHypothesis

theorem coefficient_vectorPolynomial_summable
    {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    [CompleteSpace Value] (orders : Finset ℕ) (coefficientValue : ℕ → Value) :
    Summable (fun index => coefficient index •
      vectorPolynomialEval orders coefficientValue (-node index)) :=
  (coefficient_vectorPolynomial_hasSum orders coefficientValue).summable

def IsVectorPolynomial {Value : Type*} [AddCommMonoid Value] [Module ℝ Value]
    (function : ℝ → Value) : Prop :=
  ∃ (Index : Type) (_ : Fintype Index) (degree : Index → ℕ)
      (value : Index → Value),
    ∀ scale, function scale = ∑ index, scale ^ degree index • value index

theorem IsVectorPolynomial.hasSum
    {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    [CompleteSpace Value] {function : ℝ → Value}
    (polynomial : IsVectorPolynomial function) :
    HasSum (fun index => coefficient index • function (-node index))
      (function 1) := by
  classical
  obtain ⟨Index, indexFintype, degree, value, functionSpec⟩ := polynomial
  let _ : Fintype Index := indexFintype
  have monomial (presentationIndex : Index) :
      HasSum (fun index =>
        (coefficient index * (-node index) ^ degree presentationIndex) •
          value presentationIndex) (value presentationIndex) := by
    have scalarMoment :=
      (infinite_moment_hasSum (degree presentationIndex)).smul_const
        (value presentationIndex)
    simpa only [node, one_smul] using scalarMoment
  have combined : HasSum (fun index => ∑ presentationIndex : Index,
      (coefficient index * (-node index) ^ degree presentationIndex) •
        value presentationIndex) (∑ presentationIndex : Index,
          value presentationIndex) :=
    hasSum_sum (fun presentationIndex _ => monomial presentationIndex)
  simpa only [functionSpec, Finset.smul_sum, smul_smul, one_pow, one_smul]
    using combined

theorem isVectorPolynomial_const
    {Value : Type*} [AddCommMonoid Value] [Module ℝ Value] (value : Value) :
    IsVectorPolynomial (fun _ : ℝ => value) := by
  refine ⟨PUnit, inferInstance, fun _ => 0, fun _ => value, ?_⟩
  intro scale
  simp

theorem IsVectorPolynomial.bilinear
    {First Second Target : Type*}
    [NormedAddCommGroup First] [NormedSpace ℝ First]
    [NormedAddCommGroup Second] [NormedSpace ℝ Second]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (bilinear : First →L[ℝ] Second →L[ℝ] Target)
    {first : ℝ → First} {second : ℝ → Second}
    (firstPolynomial : IsVectorPolynomial first)
    (secondPolynomial : IsVectorPolynomial second) :
    IsVectorPolynomial (fun scale => bilinear (first scale) (second scale)) := by
  classical
  obtain ⟨FirstIndex, firstFintype, firstDegree, firstValue, firstSpec⟩ :=
    firstPolynomial
  obtain ⟨SecondIndex, secondFintype, secondDegree, secondValue, secondSpec⟩ :=
    secondPolynomial
  let _ : Fintype FirstIndex := firstFintype
  let _ : Fintype SecondIndex := secondFintype
  refine ⟨FirstIndex × SecondIndex, inferInstance,
    fun index => firstDegree index.1 + secondDegree index.2,
    fun index => bilinear (firstValue index.1) (secondValue index.2), ?_⟩
  intro scale
  change bilinear (first scale) (second scale) = _
  rw [firstSpec, secondSpec, map_sum]
  simp_rw [map_smul, map_sum]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro firstIndex _
  rw [sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro secondIndex _
  simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_smul,
    pow_add]
  rw [mul_comm]

theorem IsVectorPolynomial.map
    {First Target : Type*}
    [NormedAddCommGroup First] [NormedSpace ℝ First]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (linear : First →L[ℝ] Target) {function : ℝ → First}
    (polynomial : IsVectorPolynomial function) :
    IsVectorPolynomial (fun scale => linear (function scale)) := by
  classical
  obtain ⟨Index, indexFintype, degree, value, functionSpec⟩ := polynomial
  let _ : Fintype Index := indexFintype
  refine ⟨Index, inferInstance, degree, fun index => linear (value index), ?_⟩
  intro scale
  change linear (function scale) = _
  rw [functionSpec, map_sum]
  simp only [map_smul]

theorem IsVectorPolynomial.multilinear_apply
    {arity : ℕ} {Input : Fin arity → Type*} {Target : Type*}
    [(position : Fin arity) → NormedAddCommGroup (Input position)]
    [(position : Fin arity) → NormedSpace ℝ (Input position)]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    {mapFunction : ℝ → ContinuousMultilinearMap ℝ Input Target}
    (mapPolynomial : IsVectorPolynomial mapFunction)
    (input : (position : Fin arity) → ℝ → Input position)
    (inputPolynomial : ∀ position,
      IsVectorPolynomial (input position)) :
    IsVectorPolynomial (fun scale =>
      mapFunction scale (fun position => input position scale)) := by
  induction arity with
  | zero =>
      have mapped := mapPolynomial.map
        (ContinuousMultilinearMap.apply ℝ Input Target 0)
      convert mapped using 1
      funext scale
      change mapFunction scale (fun position => input position scale) =
        mapFunction scale 0
      congr
      funext position
      exact Fin.elim0 position
  | succ arity inductionHypothesis =>
      let TailInput : Fin arity → Type _ := fun position => Input position.succ
      let TailMap := ContinuousMultilinearMap ℝ TailInput Target
      let curry : ContinuousMultilinearMap ℝ Input Target →L[ℝ]
          Input 0 →L[ℝ] TailMap :=
        (continuousMultilinearCurryLeftEquiv ℝ
          Input Target).toContinuousLinearEquiv.toContinuousLinearMap
      have curryPolynomial : IsVectorPolynomial (fun scale =>
          curry (mapFunction scale)) := by
        classical
        obtain ⟨Index, indexFintype, degree, value, mapSpec⟩ := mapPolynomial
        let _ : Fintype Index := indexFintype
        refine ⟨Index, inferInstance, degree,
          fun index => curry (value index), ?_⟩
        intro scale
        change curry (mapFunction scale) = _
        rw [mapSpec, map_sum]
        simp only [map_smul]
      let evaluation : (Input 0 →L[ℝ] TailMap) →L[ℝ]
          Input 0 →L[ℝ] TailMap :=
        (ContinuousLinearMap.apply ℝ TailMap).flip
      have headPolynomial : IsVectorPolynomial (fun scale =>
          curry (mapFunction scale) (input 0 scale)) := by
        exact IsVectorPolynomial.bilinear
          (First := Input 0 →L[ℝ] TailMap) (Second := Input 0)
          (Target := TailMap) evaluation curryPolynomial
          (inputPolynomial 0)
      have tailPolynomial : ∀ position : Fin arity,
          IsVectorPolynomial (input position.succ) :=
        fun position => inputPolynomial position.succ
      have applied := inductionHypothesis
        (mapFunction := fun scale =>
          curry (mapFunction scale) (input 0 scale)) headPolynomial
        (fun position => input position.succ) tailPolynomial
      convert applied using 1
      funext scale
      change mapFunction scale (fun position => input position scale) =
        mapFunction scale (Fin.cases (input 0 scale)
          (fun position => input position.succ scale))
      congr
      funext position
      exact Fin.cases rfl (fun _ => rfl) position

theorem IsVectorPolynomial.add
    {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {first second : ℝ → Value}
    (firstPolynomial : IsVectorPolynomial first)
    (secondPolynomial : IsVectorPolynomial second) :
    IsVectorPolynomial (fun scale => first scale + second scale) := by
  classical
  obtain ⟨FirstIndex, firstFintype, firstDegree, firstValue, firstSpec⟩ :=
    firstPolynomial
  obtain ⟨SecondIndex, secondFintype, secondDegree, secondValue, secondSpec⟩ :=
    secondPolynomial
  let _ : Fintype FirstIndex := firstFintype
  let _ : Fintype SecondIndex := secondFintype
  refine ⟨FirstIndex ⊕ SecondIndex, inferInstance,
    Sum.elim firstDegree secondDegree, Sum.elim firstValue secondValue, ?_⟩
  intro scale
  change first scale + second scale = _
  rw [firstSpec, secondSpec, Fintype.sum_sum_type]
  rfl

theorem isVectorPolynomial_finset_sum
    {Index Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (indices : Finset Index) (function : Index → ℝ → Value)
    (polynomial : ∀ index ∈ indices, IsVectorPolynomial (function index)) :
    IsVectorPolynomial (fun scale => ∑ index ∈ indices, function index scale) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      simpa using isVectorPolynomial_const (0 : Value)
  | @insert index indices fresh inductionHypothesis =>
      simp_rw [Finset.sum_insert fresh]
      exact (polynomial index (Finset.mem_insert_self index indices)).add
        (inductionHypothesis fun other otherMembership =>
          polynomial other (Finset.mem_insert_of_mem otherMembership))

theorem isVectorPolynomial_iteratedFDeriv_collarInterpolation (order : ℕ)
    (point : SpatialCell) (nonzero : planarPart point ≠ 0) :
    IsVectorPolynomial (fun parameter =>
      iteratedFDeriv ℝ order (collarInterpolation parameter) point) := by
  let normalizedJet := iteratedFDeriv ℝ order normalizedSpatialCell point
  let identityJet := iteratedFDeriv ℝ order id point
  refine ⟨Fin 2, inferInstance, fun position => position.val,
    fun position => if position = 0 then normalizedJet else identityJet - normalizedJet, ?_⟩
  intro parameter
  change iteratedFDeriv ℝ order (collarInterpolation parameter) point = _
  rw [iteratedFDeriv_collarInterpolation order parameter point nonzero,
    Fin.sum_univ_two]
  dsimp only [normalizedJet, identityJet]
  simp
  module

theorem isVectorPolynomial_closedTaylorSeries_taylorComp_collarInterpolation
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (nonzero : planarPart point ≠ 0) :
    IsVectorPolynomial (fun parameter =>
      ((closedTaylorSeries field point).taylorComp
        (fun innerOrder => iteratedFDeriv ℝ innerOrder
          (collarInterpolation parameter) point)) order) := by
  classical
  unfold FormalMultilinearSeries.taylorComp
  apply isVectorPolynomial_finset_sum Finset.univ
  intro partition _
  let partitionOperator :=
    partition.compAlongOrderedFinpartitionL ℝ SpatialCell SpatialCell
      (ComplexEuclidean dimension) (closedTaylorSeries field point partition.length)
  have operatorPolynomial : IsVectorPolynomial
      (fun _ : ℝ => partitionOperator) :=
    isVectorPolynomial_const partitionOperator
  have inputPolynomial : ∀ position : Fin partition.length,
      IsVectorPolynomial (fun parameter =>
        iteratedFDeriv ℝ (partition.partSize position)
          (collarInterpolation parameter) point) :=
    fun position => isVectorPolynomial_iteratedFDeriv_collarInterpolation
      (partition.partSize position) point nonzero
  have applied := operatorPolynomial.multilinear_apply
    (fun position parameter => iteratedFDeriv ℝ
      (partition.partSize position) (collarInterpolation parameter) point)
    inputPolynomial
  simpa only [partitionOperator,
    OrderedFinpartition.compAlongOrderedFinpartitionL_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition] using applied

theorem coefficient_closedTaylorSeries_taylorComp_collarInterpolation_hasSum
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (nonzero : planarPart point ≠ 0) :
    HasSum (fun index => coefficient index •
        ((closedTaylorSeries field point).taylorComp
          (fun innerOrder => iteratedFDeriv ℝ innerOrder
            (collarInterpolation (-node index)) point)) order)
      (((closedTaylorSeries field point).taylorComp
        (fun innerOrder => iteratedFDeriv ℝ innerOrder
          (collarInterpolation 1) point)) order) :=
  (isVectorPolynomial_closedTaylorSeries_taylorComp_collarInterpolation
    field order point nonzero).hasSum

theorem coefficient_closedTaylorSeries_taylorComp_reflectedSpatialCell_hasSum
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (nonzero : planarPart point ≠ 0) :
    HasSum (fun index => coefficient index •
        ((closedTaylorSeries field point).taylorComp
          (fun innerOrder => iteratedFDeriv ℝ innerOrder
            (reflectedSpatialCell index) point)) order)
      (((closedTaylorSeries field point).taylorComp
        (fun innerOrder => iteratedFDeriv ℝ innerOrder id point)) order) := by
  have reconstruction :=
    coefficient_closedTaylorSeries_taylorComp_collarInterpolation_hasSum
      field order point nonzero
  have oneFunction : collarInterpolation 1 = (id : SpatialCell → SpatialCell) := by
    funext candidate
    exact collarInterpolation_one candidate
  rw [oneFunction] at reconstruction
  have termEquality : (fun index => coefficient index •
      ((closedTaylorSeries field point).taylorComp
        (fun innerOrder => iteratedFDeriv ℝ innerOrder
          (collarInterpolation (-node index)) point)) order) =
      fun index => coefficient index •
        ((closedTaylorSeries field point).taylorComp
          (fun innerOrder => iteratedFDeriv ℝ innerOrder
            (reflectedSpatialCell index) point)) order := by
    funext index
    have nonzeroNeighborhood : ∀ᶠ candidate in 𝓝 point,
        planarPart candidate ≠ 0 :=
      continuous_planarPart.continuousAt.eventually
        (isOpen_compl_singleton.mem_nhds nonzero)
    have localEquality : collarInterpolation (-node index) =ᶠ[𝓝 point]
        reflectedSpatialCell index := by
      filter_upwards [nonzeroNeighborhood] with candidate candidateNonzero
      exact collarInterpolation_neg_node index candidate candidateNonzero
    have seriesEquality :
        (fun innerOrder => iteratedFDeriv ℝ innerOrder
          (collarInterpolation (-node index)) point) =
        fun innerOrder => iteratedFDeriv ℝ innerOrder
          (reflectedSpatialCell index) point := by
      funext innerOrder
      exact (localEquality.iteratedFDeriv ℝ innerOrder).eq_of_nhds
    rw [seriesEquality]
  rw [termEquality] at reconstruction
  exact reconstruction

theorem closedUnitCylinder_convex : Convex ℝ closedUnitCylinder := by
  intro first firstMembership second secondMembership firstWeight secondWeight
    firstNonnegative secondNonnegative weightSum
  change ‖planarPart (firstWeight • first + secondWeight • second)‖ ≤ 1
  have planarLinear :
      planarPart (firstWeight • first + secondWeight • second) =
        firstWeight • planarPart first + secondWeight • planarPart second := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [planarPart]
  rw [planarLinear]
  calc
    ‖firstWeight • planarPart first + secondWeight • planarPart second‖
        ≤ ‖firstWeight • planarPart first‖ +
            ‖secondWeight • planarPart second‖ := norm_add_le _ _
    _ = firstWeight * ‖planarPart first‖ +
        secondWeight * ‖planarPart second‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg firstNonnegative, abs_of_nonneg secondNonnegative]
    _ ≤ firstWeight * 1 + secondWeight * 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left firstMembership firstNonnegative)
        (mul_le_mul_of_nonneg_left secondMembership secondNonnegative)
    _ = 1 := by linarith

theorem closedUnitCylinder_interior_nonempty :
    (interior closedUnitCylinder).Nonempty := by
  refine ⟨0, ?_⟩
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset
    (openUnitCylinder_isOpen.mem_nhds (by
      change ‖planarPart (0 : SpatialCell)‖ < 1
      have planarZero : planarPart (0 : SpatialCell) = 0 := by
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp [planarPart]
      rw [planarZero, norm_zero]
      norm_num))
    (fun _ membership => openCylinderMembershipClosed _ membership)

theorem closedUnitCylinder_uniqueDiffOn :
    UniqueDiffOn ℝ closedUnitCylinder :=
  uniqueDiffOn_convex closedUnitCylinder_convex
    closedUnitCylinder_interior_nonempty

theorem closedTaylorSeries_taylorComp_identity
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (point : SpatialCell) (membership : point ∈ closedUnitCylinder)
    (order : ℕ) :
    ((closedTaylorSeries field point).taylorComp
      (fun innerOrder => iteratedFDeriv ℝ innerOrder id point)) order =
      closedTaylorSeries field point order := by
  change ((closedTaylorSeries field point).taylorComp
    (ftaylorSeries ℝ id point)) order = closedTaylorSeries field point order
  have identityTaylor : HasFTaylorSeriesUpToOn (𝕜 := ℝ) ∞
      (id : SpatialCell → SpatialCell) (ftaylorSeries ℝ id)
      closedUnitCylinder :=
    contDiff_id.ftaylorSeries.hasFTaylorSeriesUpToOn closedUnitCylinder
  have composed := (diskCellLift_hasFTaylorSeriesUpToOn_closed field).comp
    identityTaylor (mapsTo_id closedUnitCylinder)
  have composedCoefficient :=
    composed.eq_iteratedFDerivWithin_of_uniqueDiffOn
      (m := order)
      (WithTop.coe_le_coe.mpr
        (show (order : ℕ∞) ≤ ⊤ from le_top))
      closedUnitCylinder_uniqueDiffOn membership
  have originalCoefficient :=
    (diskCellLift_hasFTaylorSeriesUpToOn_closed field).eq_iteratedFDerivWithin_of_uniqueDiffOn
        (m := order)
        (WithTop.coe_le_coe.mpr
          (show (order : ℕ∞) ≤ ⊤ from le_top))
        closedUnitCylinder_uniqueDiffOn membership
  simpa only [id_eq, Function.comp_id] using
    composedCoefficient.trans originalCoefficient.symm

theorem coefficient_closedTaylorSeries_taylorComp_reflectedSpatialCell_hasSum_closed
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    HasSum (fun index => coefficient index •
        ((closedTaylorSeries field point).taylorComp
          (fun innerOrder => iteratedFDeriv ℝ innerOrder
            (reflectedSpatialCell index) point)) order)
      (closedHigherDerivative (order := order) field point) := by
  have nonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at boundary
    norm_num at boundary
  have reconstruction :=
    coefficient_closedTaylorSeries_taylorComp_reflectedSpatialCell_hasSum
      field order point nonzero
  have membership : point ∈ closedUnitCylinder := by
    change ‖planarPart point‖ ≤ 1
    exact boundary.le
  rw [closedTaylorSeries_taylorComp_identity field point membership order]
    at reconstruction
  simpa only [closedTaylorSeries] using reconstruction

def planarNonzeroRegion : Set SpatialCell :=
  {point | planarPart point ≠ 0}

theorem planarNonzeroRegion_isOpen : IsOpen planarNonzeroRegion := by
  change IsOpen (planarPart ⁻¹' ({0} : Set SpatialPlane)ᶜ)
  exact (isClosed_singleton.isOpen_compl.preimage continuous_planarPart)

theorem reflectedSpatialCell_contDiffOn_planarNonzeroRegion (index : ℕ) :
    ContDiffOn ℝ ∞ (reflectedSpatialCell index) planarNonzeroRegion := by
  intro point nonzero
  exact (reflectedSpatialCell_contDiffAt index point nonzero).contDiffWithinAt

theorem reflectedSpatialCell_hasFTaylorSeriesUpToOn_planarNonzeroRegion
    (index : ℕ) :
    HasFTaylorSeriesUpToOn (𝕜 := ℝ) ∞ (reflectedSpatialCell index)
      (ftaylorSeries ℝ (reflectedSpatialCell index)) planarNonzeroRegion := by
  have withinTaylor :=
    (reflectedSpatialCell_contDiffOn_planarNonzeroRegion index).ftaylorSeriesWithin
      planarNonzeroRegion_isOpen.uniqueDiffOn
  apply withinTaylor.congr_series
  intro order _ point membership
  exact iteratedFDerivWithin_of_isOpen order planarNonzeroRegion_isOpen
    membership

theorem closedExteriorActiveRegion_subset_planarNonzeroRegion (index : ℕ) :
    closedExteriorActiveRegion index ⊆ planarNonzeroRegion := by
  intro point membership
  exact closedExteriorActiveRegion_planarPart_ne_zero index membership

theorem reflectedSpatialCell_hasFTaylorSeriesUpToOn_active (index : ℕ) :
    HasFTaylorSeriesUpToOn (𝕜 := ℝ) ∞ (reflectedSpatialCell index)
      (ftaylorSeries ℝ (reflectedSpatialCell index))
      (closedExteriorActiveRegion index) :=
  (reflectedSpatialCell_hasFTaylorSeriesUpToOn_planarNonzeroRegion index).mono
    (closedExteriorActiveRegion_subset_planarNonzeroRegion index)

theorem diskCellLift_comp_reflectedSpatialCell_hasFTaylorSeriesUpToOn_active
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (index : ℕ) :
    HasFTaylorSeriesUpToOn (𝕜 := ℝ) ∞
      (diskCellLift field.value ∘ reflectedSpatialCell index)
      (fun point => (closedTaylorSeries field (reflectedSpatialCell index point)).taylorComp
        (ftaylorSeries ℝ (reflectedSpatialCell index) point))
      (closedExteriorActiveRegion index) :=
  (diskCellLift_hasFTaylorSeriesUpToOn_closed field).comp
    (reflectedSpatialCell_hasFTaylorSeriesUpToOn_active index)
    (fun _ membership =>
      reflectedSpatialCell_mem_closedUnitCylinder_active index membership)

theorem coefficient_collarInterpolation_iteratedFDeriv_hasSum (order : ℕ)
    (point : SpatialCell) (nonzero : planarPart point ≠ 0) :
    HasSum (fun index => coefficient index •
        iteratedFDeriv ℝ order (collarInterpolation (-node index)) point)
      (iteratedFDeriv ℝ order (collarInterpolation 1) point) := by
  let coefficientValue : ℕ →
      SpatialCell [×order]→L[ℝ] SpatialCell := fun degree =>
    if degree = 0 then iteratedFDeriv ℝ order normalizedSpatialCell point
    else if degree = 1 then iteratedFDeriv ℝ order id point -
      iteratedFDeriv ℝ order normalizedSpatialCell point
    else 0
  have reconstruction := coefficient_vectorPolynomial_hasSum
    ({0, 1} : Finset ℕ) coefficientValue
  simpa only [coefficientValue,
    ← iteratedFDeriv_collarInterpolation_vectorPolynomial order _ point nonzero]
    using reconstruction

theorem coefficient_reflectedSpatialCell_iteratedFDeriv_hasSum (order : ℕ)
    (point : SpatialCell) (nonzero : planarPart point ≠ 0) :
    HasSum (fun index => coefficient index •
        iteratedFDeriv ℝ order (reflectedSpatialCell index) point)
      (iteratedFDeriv ℝ order id point) := by
  have reconstruction :=
    coefficient_collarInterpolation_iteratedFDeriv_hasSum order point nonzero
  have oneFunction : collarInterpolation 1 = (id : SpatialCell → SpatialCell) := by
    funext candidate
    exact collarInterpolation_one candidate
  rw [oneFunction] at reconstruction
  have termEquality : (fun index => coefficient index •
      iteratedFDeriv ℝ order (collarInterpolation (-node index)) point) =
      fun index => coefficient index •
        iteratedFDeriv ℝ order (reflectedSpatialCell index) point := by
    funext index
    have nonzeroNeighborhood : ∀ᶠ candidate in 𝓝 point,
        planarPart candidate ≠ 0 :=
      continuous_planarPart.continuousAt.eventually
        (isOpen_compl_singleton.mem_nhds nonzero)
    have localEquality : collarInterpolation (-node index) =ᶠ[𝓝 point]
        reflectedSpatialCell index := by
      filter_upwards [nonzeroNeighborhood] with candidate candidateNonzero
      exact collarInterpolation_neg_node index candidate candidateNonzero
    congr 1
    exact (localEquality.iteratedFDeriv ℝ order).eq_of_nhds
  rw [termEquality] at reconstruction
  exact reconstruction

end Grad.DiskExtension.Operator
