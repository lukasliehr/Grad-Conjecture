import FP17DiskSup
import SP1Words
import Mathlib.LinearAlgebra.Multilinear.Basis

noncomputable section

open Filter Set
open scoped BigOperators ContDiff Topology

namespace Grad.CartesianState

open Grad.ClosedJets
open Grad.PDEBootstrap
open Grad.RepresentedKernel.SpatialProduct

/-- Coordinate coefficient of a multilinear form in the fixed orthonormal
basis of the physical disk plane. -/
def spatialPlaneWordCoefficient {order : ℕ}
    (word : CartesianWord order) : SpatialPlane [×order]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ order ℝ).compContinuousLinearMap
    (fun position =>
      PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (word position))

@[simp] theorem spatialPlaneWordCoefficient_apply {order : ℕ}
    (word : CartesianWord order) (directions : Fin order → SpatialPlane) :
    spatialPlaneWordCoefficient word directions =
      (List.ofFn fun position => directions position (word position)).prod := by
  simp [spatialPlaneWordCoefficient,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]

@[simp] theorem spatialPlaneWordCoefficient_basis {order : ℕ}
    (coefficientWord word : CartesianWord order) :
    spatialPlaneWordCoefficient coefficientWord
        (fun position => spatialBasis (word position)) =
      if coefficientWord = word then 1 else 0 := by
  classical
  rw [spatialPlaneWordCoefficient_apply]
  split_ifs with equality
  · subst coefficientWord
    simp [spatialBasis]
  · apply List.prod_eq_zero
    rw [List.mem_ofFn]
    have differingPosition : ∃ position,
        coefficientWord position ≠ word position := by
      by_contra noDifferingPosition
      apply equality
      funext position
      by_contra positionDiffers
      exact (not_exists.mp noDifferingPosition position) positionDiffers
    obtain ⟨position, positionDiffers⟩ := differingPosition
    refine ⟨position, ?_⟩
    simp only [spatialBasis, Pi.single_apply]
    exact if_neg positionDiffers

/-- All ordered derivatives of a closed disk jet, assembled as one continuous
multilinear map on the ambient plane. -/
def closedPlaneHigherDerivative {dimension order : ℕ}
    (field : ClosedJet dimension) (point : SpatialPlane) :
    SpatialPlane [×order]→L[ℝ] ComplexEuclidean dimension :=
  ∑ word : CartesianWord order,
    (spatialPlaneWordCoefficient word).smulRight
      (closedDerivative field order word (ambientClosedDisk point))

theorem closedPlaneHigherDerivative_continuous {dimension order : ℕ}
    (field : ClosedJet dimension) :
    Continuous (closedPlaneHigherDerivative (order := order) field) := by
  apply continuous_finsetSum
  intro word _
  exact ((ContinuousMultilinearMap.smulRightL ℝ
      (fun _ : Fin order => SpatialPlane) (ComplexEuclidean dimension)
      (spatialPlaneWordCoefficient word)).continuous.comp
        ((closedDerivative field order word).continuous.comp
          continuous_ambientClosedDisk))

@[simp] theorem closedPlaneHigherDerivative_basis {dimension order : ℕ}
    (field : ClosedJet dimension) (point : SpatialPlane)
    (word : CartesianWord order) :
    closedPlaneHigherDerivative field point
        (fun position => spatialBasis (word position)) =
      closedDerivative field order word (ambientClosedDisk point) := by
  classical
  rw [closedPlaneHigherDerivative, sum_apply]
  rw [Finset.sum_eq_single word]
  · rw [ContinuousMultilinearMap.smulRight_apply,
      spatialPlaneWordCoefficient_basis, if_pos rfl, one_smul]
  · intro other _ otherNe
    rw [ContinuousMultilinearMap.smulRight_apply,
      spatialPlaneWordCoefficient_basis, if_neg otherNe, zero_smul]
  · simp

theorem continuousMultilinearMap_ext_spatialPlaneBasis
    {dimension order : ℕ}
    (first second : SpatialPlane [×order]→L[ℝ] ComplexEuclidean dimension)
    (basisEquality : ∀ word : CartesianWord order,
      first (fun position => spatialBasis (word position)) =
        second (fun position => spatialBasis (word position))) :
    first = second := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear
    (fun _ : Fin order => PiLp.basisFun 2 ℝ (Fin 2))
  intro word
  rw [show (fun position => PiLp.basisFun 2 ℝ (Fin 2) (word position)) =
      fun position => spatialBasis (word position) by
    funext position
    rw [PiLp.basisFun_apply]
    rfl]
  exact basisEquality word

theorem closedPlaneHigherDerivative_eq_iteratedFDeriv {dimension order : ℕ}
    (field : ClosedJet dimension) (point : SpatialPlane)
    (membership : point ∈ openUnitDisk) :
    closedPlaneHigherDerivative field point =
      iteratedFDeriv ℝ order (closedDiskLift field.value) point := by
  apply continuousMultilinearMap_ext_spatialPlaneBasis
  intro word
  rw [closedPlaneHigherDerivative_basis]
  have ambientEquality : ambientClosedDisk point =
      (⟨point, openDiskMembershipClosed point membership⟩ : ClosedDisk) := by
    apply Subtype.ext
    exact ambientClosedDisk_val_of_mem
      (openDiskMembershipClosed point membership)
  rw [ambientEquality]
  exact closedDerivative_spec field order word
    ⟨point, openDiskMembershipClosed point membership⟩ membership

theorem closedPlaneHigherDerivative_fderiv_interior {dimension order : ℕ}
    (field : ClosedJet dimension) (point : SpatialPlane)
    (membership : point ∈ openUnitDisk) :
    fderiv ℝ (closedPlaneHigherDerivative (order := order) field) point =
      (closedPlaneHigherDerivative (order := order + 1) field point).curryLeft := by
  have localEquality : closedPlaneHigherDerivative (order := order) field =ᶠ[𝓝 point]
      iteratedFDeriv ℝ order (closedDiskLift field.value) := by
    filter_upwards [openUnitDisk_isOpen.mem_nhds membership] with candidate
      candidateMembership
    exact closedPlaneHigherDerivative_eq_iteratedFDeriv
      field candidate candidateMembership
  rw [localEquality.fderiv_eq, fderiv_iteratedFDeriv]
  rw [closedPlaneHigherDerivative_eq_iteratedFDeriv
    (order := order + 1) field point membership]
  rfl

theorem closedPlaneHigherDerivative_contDiffAt_interior {dimension order : ℕ}
    (field : ClosedJet dimension) (point : SpatialPlane)
    (membership : point ∈ openUnitDisk) :
    ContDiffAt ℝ ∞ (closedPlaneHigherDerivative (order := order) field) point := by
  have localEquality : closedPlaneHigherDerivative (order := order) field =ᶠ[𝓝 point]
      iteratedFDeriv ℝ order (closedDiskLift field.value) := by
    filter_upwards [openUnitDisk_isOpen.mem_nhds membership] with candidate
      candidateMembership
    exact closedPlaneHigherDerivative_eq_iteratedFDeriv
      field candidate candidateMembership
  have smoothAt := (field.smoothInterior point membership).contDiffAt
    (openUnitDisk_isOpen.mem_nhds membership)
  have derivativeSmooth := smoothAt.iteratedFDeriv_right
    (m := ∞) (i := order) (by norm_cast)
  exact derivativeSmooth.congr_of_eventuallyEq localEquality

/-- Evaluation of the assembled ordered derivative tensor on fixed
directions. -/
def closedPlaneDerivativeEvaluation {dimension order : ℕ}
    (field : ClosedJet dimension) (directions : Fin order → SpatialPlane)
    (point : SpatialPlane) : ComplexEuclidean dimension :=
  closedPlaneHigherDerivative field point directions

theorem closedPlaneDerivativeEvaluation_fderiv {dimension order : ℕ}
    (field : ClosedJet dimension) (directions : Fin order → SpatialPlane)
    (point direction : SpatialPlane) (membership : point ∈ openUnitDisk) :
    fderiv ℝ (closedPlaneDerivativeEvaluation field directions) point direction =
      closedPlaneDerivativeEvaluation field (Fin.cons direction directions) point := by
  let evaluation :
      (SpatialPlane [×order]→L[ℝ] ComplexEuclidean dimension) →L[ℝ]
        ComplexEuclidean dimension :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin order => SpatialPlane)
      (ComplexEuclidean dimension) directions
  have compositionDerivative := evaluation.iteratedFDeriv_comp_left
    (closedPlaneHigherDerivative_contDiffAt_interior
      (order := order) field point membership)
    (i := 1) (by norm_num)
  have applied := congrArg
    (fun derivative : SpatialPlane [×1]→L[ℝ] ComplexEuclidean dimension =>
      derivative ![direction]) compositionDerivative
  change fderiv ℝ (closedPlaneDerivativeEvaluation field directions) point direction = _
  have leftIdentity :
      fderiv ℝ (closedPlaneDerivativeEvaluation field directions) point direction =
        (iteratedFDeriv ℝ 1
          (closedPlaneDerivativeEvaluation field directions) point) ![direction] := by
    rw [iteratedFDeriv_one_apply]
    rfl
  rw [leftIdentity]
  change (iteratedFDeriv ℝ 1
      (evaluation ∘ closedPlaneHigherDerivative field) point) ![direction] = _
  rw [applied]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply, evaluation, ContinuousMultilinearMap.apply_apply]
  rw [iteratedFDeriv_one_apply]
  rw [closedPlaneHigherDerivative_fderiv_interior field point membership]
  rfl

/-- A list presentation of ordered Cartesian derivatives.  It is convenient
for concatenating a new derivative word in front of a fixed old word. -/
def cartesianListDerivative {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (word : List (Fin 2))
    (function : SpatialPlane → Value) : SpatialPlane → Value :=
  word.foldr
    (fun direction derivative point =>
      fderiv ℝ derivative point (spatialBasis direction))
    function

theorem cartesianListDerivative_smooth {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set SpatialPlane} (openDomain : IsOpen domain)
    (word : List (Fin 2)) {function : SpatialPlane → Value}
    (smooth : ContDiffOn ℝ ∞ function domain) :
    ContDiffOn ℝ ∞ (cartesianListDerivative word function) domain := by
  induction word with
  | nil => exact smooth
  | cons direction rest inductionHypothesis =>
    exact ((contDiffOn_infty_iff_fderiv_of_isOpen openDomain).mp
      inductionHypothesis).2.clm_apply contDiffOn_const

theorem cartesianListDerivative_congr {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set SpatialPlane} (openDomain : IsOpen domain)
    (word : List (Fin 2)) {first second : SpatialPlane → Value}
    (agree : Set.EqOn first second domain) :
    Set.EqOn (cartesianListDerivative word first)
      (cartesianListDerivative word second) domain := by
  induction word with
  | nil => exact agree
  | cons direction rest inductionHypothesis =>
    intro point inside
    have localEquality :
        cartesianListDerivative rest first =ᶠ[𝓝 point]
          cartesianListDerivative rest second :=
      Filter.eventually_of_mem (openDomain.mem_nhds inside)
        inductionHypothesis
    exact congrArg
      (fun derivative : SpatialPlane →L[ℝ] Value =>
        derivative (spatialBasis direction))
      localEquality.fderiv_eq

theorem cartesianListDerivative_ofFn {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set SpatialPlane} (openDomain : IsOpen domain)
    (order : ℕ) (word : CartesianWord order)
    {function : SpatialPlane → Value}
    (smooth : ContDiffOn ℝ ∞ function domain) :
    Set.EqOn (cartesianListDerivative (List.ofFn word) function)
      (cartesianDerivative order word function) domain := by
  induction order with
  | zero => exact fun _ _ => rfl
  | succ order inductionHypothesis =>
    intro point inside
    rw [List.ofFn_succ]
    have congruence := cartesianListDerivative_congr openDomain [word 0]
      (inductionHypothesis (Fin.tail word)) inside
    refine congruence.trans ?_
    exact ((differentiable_iterated
      (smooth.contDiffAt (openDomain.mem_nhds inside)) order).iteratedFDeriv_succ_apply_left'
        (m := fun position => spatialBasis (word position))).symm

theorem cartesianListDerivative_append {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (first second : List (Fin 2)) (function : SpatialPlane → Value) :
    cartesianListDerivative (first ++ second) function =
      cartesianListDerivative first
        (cartesianListDerivative second function) := by
  induction first with
  | nil => rfl
  | cons direction rest inductionHypothesis =>
    funext point
    change fderiv ℝ (cartesianListDerivative (rest ++ second) function)
      point (spatialBasis direction) =
        fderiv ℝ (cartesianListDerivative rest
          (cartesianListDerivative second function))
            point (spatialBasis direction)
    rw [inductionHypothesis]

theorem cartesianList_counts (word : List (Fin 2)) :
    word.count 0 + word.count 1 = word.length := by
  induction word with
  | nil => simp
  | cons direction rest inductionHypothesis =>
    fin_cases direction <;> simp_all <;> omega

theorem cartesianList_canonical_perm (word : List (Fin 2)) :
    word.Perm
      (List.replicate (word.count 0) 0 ++
        List.replicate (word.count 1) 1) := by
  apply List.perm_iff_count.mpr
  intro direction
  fin_cases direction <;> simp [List.count_replicate]

def cartesianWordIndex {order : ℕ} (word : CartesianWord order) :
    CartesianMultiIndex :=
  ((List.ofFn word).count 0, (List.ofFn word).count 1)

theorem cartesianWordIndex_order {order : ℕ}
    (word : CartesianWord order) :
    cartesianOrder (cartesianWordIndex word) = order := by
  simpa [cartesianWordIndex, cartesianOrder] using
    cartesianList_counts (List.ofFn word)

theorem list_ofFn_cartesianMultiIndexWord (index : CartesianMultiIndex) :
    List.ofFn (cartesianMultiIndexWord index) =
      List.replicate index.1 0 ++ List.replicate index.2 1 := by
  apply List.ext_get
  · rw [List.length_ofFn, List.length_append,
      List.length_replicate, List.length_replicate]
    rfl
  · intro position firstBound secondBound
    simp only [List.get_eq_getElem]
    by_cases beforeSplit : position < index.1
    · rw [List.getElem_append_left (by simpa using beforeSplit)]
      simp [cartesianMultiIndexWord, beforeSplit]
    · rw [List.getElem_append_right (by
        simpa using Nat.le_of_not_gt beforeSplit)]
      simp [cartesianMultiIndexWord, beforeSplit]

theorem cartesianWord_canonical_perm {order : ℕ}
    (word : CartesianWord order) :
    (List.ofFn word).Perm
      (List.ofFn (cartesianMultiIndexWord (cartesianWordIndex word))) := by
  rw [list_ofFn_cartesianMultiIndexWord]
  exact cartesianList_canonical_perm (List.ofFn word)

theorem cartesianListDerivative_perm {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set SpatialPlane} (openDomain : IsOpen domain)
    {first second : List (Fin 2)} (permuted : first.Perm second)
    {function : SpatialPlane → Value}
    (smooth : ContDiffOn ℝ ∞ function domain) :
    Set.EqOn (cartesianListDerivative first function)
      (cartesianListDerivative second function) domain := by
  induction permuted with
  | nil => exact fun _ _ => rfl
  | cons direction permuted inductionHypothesis =>
    exact cartesianListDerivative_congr openDomain [direction]
      inductionHypothesis
  | swap first second rest =>
    intro point inside
    have restSmooth := cartesianListDerivative_smooth
      openDomain rest smooth
    have localSmooth := restSmooth.contDiffAt
      (openDomain.mem_nhds inside)
    have derivativeSmooth :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen openDomain).mp
        restSmooth).2
    have derivativeDifferentiable :=
      (derivativeSmooth.contDiffAt
        (openDomain.mem_nhds inside)).differentiableAt (by simp)
    simp only [cartesianListDerivative, List.foldr_cons]
    change fderiv ℝ (fun source => fderiv ℝ
        (cartesianListDerivative rest function) source
          (spatialBasis first)) point (spatialBasis second) =
      fderiv ℝ (fun source => fderiv ℝ
        (cartesianListDerivative rest function) source
          (spatialBasis second)) point (spatialBasis first)
    rw [fderiv_clm_apply derivativeDifferentiable
        (differentiableAt_const (spatialBasis second)),
      fderiv_clm_apply derivativeDifferentiable
        (differentiableAt_const (spatialBasis first))]
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero,
      zero_add, ContinuousLinearMap.flip_apply]
    exact (localSmooth.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eq _ _
  | trans first second inductionFirst inductionSecond =>
    exact inductionFirst.trans inductionSecond

theorem closedDerivative_eq_closedMultiDerivative_wordIndex
    {dimension order : ℕ} (field : ClosedJet dimension)
    (word : CartesianWord order) :
    closedDerivative field order word =
      closedMultiDerivative field (cartesianWordIndex word) := by
  apply continuousMap_eq_of_openDisk
  intro point membership
  rw [closedDerivative_spec field order word point membership]
  rw [closedMultiDerivative,
    closedDerivative_spec field
      (cartesianOrder (cartesianWordIndex word))
      (cartesianMultiIndexWord (cartesianWordIndex word)) point membership]
  calc
    cartesianDerivative order word (closedDiskLift field.value) point.val =
        cartesianListDerivative (List.ofFn word)
          (closedDiskLift field.value) point.val :=
      (cartesianListDerivative_ofFn openUnitDisk_isOpen order word
        field.smoothInterior membership).symm
    _ = cartesianListDerivative
        (List.ofFn (cartesianMultiIndexWord (cartesianWordIndex word)))
          (closedDiskLift field.value) point.val :=
      cartesianListDerivative_perm openUnitDisk_isOpen
        (cartesianWord_canonical_perm word) field.smoothInterior membership
    _ = cartesianDerivative (cartesianOrder (cartesianWordIndex word))
        (cartesianMultiIndexWord (cartesianWordIndex word))
          (closedDiskLift field.value) point.val :=
      cartesianListDerivative_ofFn openUnitDisk_isOpen
        (cartesianOrder (cartesianWordIndex word))
        (cartesianMultiIndexWord (cartesianWordIndex word))
          field.smoothInterior membership

/-- The value of the closed jet obtained by fixing an old ordered derivative
word. -/
def shiftedClosedJetValue {dimension order : ℕ}
    (field : ClosedJet dimension) (word : CartesianWord order) :
    ContinuousMap ClosedDisk (ComplexEuclidean dimension) :=
  closedDerivative field order word

theorem closedDiskLift_shiftedClosedJetValue_interior
    {dimension order : ℕ} (field : ClosedJet dimension)
    (word : CartesianWord order) (point : SpatialPlane)
    (membership : point ∈ openUnitDisk) :
    closedDiskLift (shiftedClosedJetValue field word) point =
      cartesianListDerivative (List.ofFn word)
        (closedDiskLift field.value) point := by
  rw [show closedDiskLift (shiftedClosedJetValue field word) point =
      shiftedClosedJetValue field word
        ⟨point, openDiskMembershipClosed point membership⟩ by
    simp [closedDiskLift, openDiskMembershipClosed point membership]]
  rw [shiftedClosedJetValue,
    closedDerivative_spec field order word
      ⟨point, openDiskMembershipClosed point membership⟩ membership]
  exact (cartesianListDerivative_ofFn openUnitDisk_isOpen order word
    field.smoothInterior membership).symm

theorem shiftedClosedJetValue_smoothInterior {dimension order : ℕ}
    (field : ClosedJet dimension) (word : CartesianWord order) :
    ContDiffOn ℝ ∞ (closedDiskLift (shiftedClosedJetValue field word))
      openUnitDisk := by
  apply (cartesianListDerivative_smooth openUnitDisk_isOpen
    (List.ofFn word) field.smoothInterior).congr
  intro point membership
  exact closedDiskLift_shiftedClosedJetValue_interior
    field word point membership

def shiftedClosedJetDerivativeValue {dimension order : ℕ}
    (field : ClosedJet dimension) (word : CartesianWord order)
    (newOrder : ℕ) (newWord : CartesianWord newOrder) :
    ContinuousMap ClosedDisk (ComplexEuclidean dimension) :=
  closedDerivative field (newOrder + order) (Fin.append newWord word)

theorem shiftedClosedJetDerivativeValue_spec {dimension order : ℕ}
    (field : ClosedJet dimension) (word : CartesianWord order)
    (newOrder : ℕ) (newWord : CartesianWord newOrder) :
    IsCartesianExtension (shiftedClosedJetValue field word)
      newOrder newWord
        (shiftedClosedJetDerivativeValue field word newOrder newWord) := by
  intro point membership
  rw [shiftedClosedJetDerivativeValue,
    closedDerivative_spec field (newOrder + order)
      (Fin.append newWord word) point membership]
  have localEquality :
      closedDiskLift (shiftedClosedJetValue field word) =ᶠ[𝓝 point.val]
        cartesianListDerivative (List.ofFn word)
          (closedDiskLift field.value) := by
    filter_upwards [openUnitDisk_isOpen.mem_nhds membership] with candidate
      candidateMembership
    exact closedDiskLift_shiftedClosedJetValue_interior
      field word candidate candidateMembership
  have derivativeEquality :=
    (localEquality.iteratedFDeriv ℝ newOrder).self_of_nhds
  change _ = (iteratedFDeriv ℝ newOrder
    (closedDiskLift (shiftedClosedJetValue field word)) point.val)
      (fun position => spatialBasis (newWord position))
  rw [derivativeEquality]
  have oldSmooth := cartesianListDerivative_smooth openUnitDisk_isOpen
    (List.ofFn word) field.smoothInterior
  change cartesianDerivative (newOrder + order) (Fin.append newWord word)
      (closedDiskLift field.value) point.val =
    cartesianDerivative newOrder newWord
      (cartesianListDerivative (List.ofFn word)
        (closedDiskLift field.value)) point.val
  rw [← cartesianListDerivative_ofFn openUnitDisk_isOpen newOrder newWord
    oldSmooth membership]
  rw [← cartesianListDerivative_append]
  rw [← List.ofFn_fin_append]
  exact (cartesianListDerivative_ofFn openUnitDisk_isOpen
    (newOrder + order) (Fin.append newWord word)
      field.smoothInterior membership).symm

/-- Fixing an arbitrary ordered Cartesian derivative of a closed jet again
produces a closed jet.  Its new ordered derivatives are the concatenated
derivatives of the original jet. -/
def shiftedClosedJet {dimension order : ℕ} (field : ClosedJet dimension)
    (word : CartesianWord order) : ClosedJet dimension where
  value := shiftedClosedJetValue field word
  smoothInterior := shiftedClosedJetValue_smoothInterior field word
  derivativeExists := by
    intro newOrder newWord
    exact ⟨shiftedClosedJetDerivativeValue field word newOrder newWord,
      shiftedClosedJetDerivativeValue_spec field word newOrder newWord⟩

@[simp] theorem shiftedClosedJet_value {dimension order : ℕ}
    (field : ClosedJet dimension) (word : CartesianWord order) :
    (shiftedClosedJet field word).value = closedDerivative field order word :=
  rfl

theorem shiftedClosedJet_closedDerivative {dimension order : ℕ}
    (field : ClosedJet dimension) (word : CartesianWord order)
    (newOrder : ℕ) (newWord : CartesianWord newOrder) :
    closedDerivative (shiftedClosedJet field word) newOrder newWord =
      closedDerivative field (newOrder + order) (Fin.append newWord word) := by
  symm
  apply cartesianExtension_unique
  exact shiftedClosedJetDerivativeValue_spec field word newOrder newWord

def shiftedCartesianIndex {order : ℕ} (word : CartesianWord order)
    (index : CartesianMultiIndex) : CartesianMultiIndex :=
  cartesianWordIndex
    (Fin.append (cartesianMultiIndexWord index) word)

theorem shiftedCartesianIndex_order {order : ℕ}
    (word : CartesianWord order) (index : CartesianMultiIndex) :
    cartesianOrder (shiftedCartesianIndex word index) =
      cartesianOrder index + order := by
  exact cartesianWordIndex_order
    (Fin.append (cartesianMultiIndexWord index) word)

theorem shiftedClosedJet_closedMultiDerivative {dimension order : ℕ}
    (field : ClosedJet dimension) (word : CartesianWord order)
    (index : CartesianMultiIndex) :
    closedMultiDerivative (shiftedClosedJet field word) index =
      closedMultiDerivative field (shiftedCartesianIndex word index) := by
  rw [closedMultiDerivative,
    shiftedClosedJet_closedDerivative field word
      (cartesianOrder index) (cartesianMultiIndexWord index)]
  exact closedDerivative_eq_closedMultiDerivative_wordIndex field
    (Fin.append (cartesianMultiIndexWord index) word)

end Grad.CartesianState
