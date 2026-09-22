import GC13Interface
import SP1Words

noncomputable section

set_option maxHeartbeats 5000000

open Filter Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.RepresentedKernel.SpatialProduct
open scoped ContDiff Topology

namespace Grad.GaugeCoefficients.Radial

open Grad.GaugeCoefficients.Algebra

def operatorCartesianListDerivative {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (word : List (Fin 2)) (function : SpatialPlane → Value) : SpatialPlane → Value :=
  word.foldr
    (fun direction derivative point =>
      fderiv ℝ derivative point (spatialBasis direction))
    function

theorem operatorCartesianListDerivative_smooth {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set SpatialPlane} (openDomain : IsOpen domain)
    (word : List (Fin 2)) {function : SpatialPlane → Value}
    (smooth : ContDiffOn ℝ ∞ function domain) :
    ContDiffOn ℝ ∞ (operatorCartesianListDerivative word function) domain := by
  induction word with
  | nil => exact smooth
  | cons direction rest inductionHypothesis =>
    exact ((contDiffOn_infty_iff_fderiv_of_isOpen openDomain).mp
      inductionHypothesis).2.clm_apply contDiffOn_const

theorem operatorCartesianListDerivative_congr {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set SpatialPlane} (openDomain : IsOpen domain)
    (directionsList : List (Fin 2)) {first second : SpatialPlane → Value}
    (agreement : Set.EqOn first second domain) :
    Set.EqOn (operatorCartesianListDerivative directionsList first)
      (operatorCartesianListDerivative directionsList second) domain := by
  induction directionsList with
  | nil => exact agreement
  | cons direction rest inductionHypothesis =>
    intro point inside
    have localEquality :
        operatorCartesianListDerivative rest first =ᶠ[𝓝 point]
          operatorCartesianListDerivative rest second :=
      Filter.eventually_of_mem (openDomain.mem_nhds inside) inductionHypothesis
    exact congrArg
      (fun derivative : SpatialPlane →L[ℝ] Value =>
        derivative (spatialBasis direction)) localEquality.fderiv_eq

theorem operatorCartesianListDerivative_ofFn {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set SpatialPlane} (openDomain : IsOpen domain)
    (order : ℕ) (word : CartesianWord order)
    {function : SpatialPlane → Value}
    (smooth : ContDiffOn ℝ ∞ function domain) :
    Set.EqOn (operatorCartesianListDerivative (List.ofFn word) function)
      (cartesianDerivative order word function) domain := by
  induction order with
  | zero => exact fun _ _ => rfl
  | succ order inductionHypothesis =>
    intro point inside
    rw [List.ofFn_succ]
    have congruence := operatorCartesianListDerivative_congr openDomain [word 0]
      (inductionHypothesis (Fin.tail word)) inside
    refine congruence.trans ?_
    exact ((differentiable_iterated
      (smooth.contDiffAt (openDomain.mem_nhds inside)) order).iteratedFDeriv_succ_apply_left'
        (m := fun position => spatialBasis (word position))).symm

theorem operatorCartesianListDerivative_append {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (first second : List (Fin 2)) (function : SpatialPlane → Value) :
    operatorCartesianListDerivative (first ++ second) function =
      operatorCartesianListDerivative first
        (operatorCartesianListDerivative second function) := by
  induction first with
  | nil => rfl
  | cons direction rest inductionHypothesis =>
    funext point
    change fderiv ℝ (operatorCartesianListDerivative (rest ++ second) function)
      point (spatialBasis direction) =
        fderiv ℝ (operatorCartesianListDerivative rest
          (operatorCartesianListDerivative second function)) point
            (spatialBasis direction)
    rw [inductionHypothesis]

theorem operatorCartesianListDerivative_perm {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set SpatialPlane} (openDomain : IsOpen domain)
    {first second : List (Fin 2)} (permuted : first.Perm second)
    {function : SpatialPlane → Value}
    (smooth : ContDiffOn ℝ ∞ function domain) :
    Set.EqOn (operatorCartesianListDerivative first function)
      (operatorCartesianListDerivative second function) domain := by
  induction permuted with
  | nil => exact fun _ _ => rfl
  | cons direction permuted inductionHypothesis =>
    exact operatorCartesianListDerivative_congr openDomain [direction]
      inductionHypothesis
  | swap first second rest =>
    intro point inside
    have restSmooth := operatorCartesianListDerivative_smooth
      openDomain rest smooth
    have localSmooth := restSmooth.contDiffAt (openDomain.mem_nhds inside)
    have derivativeSmooth :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen openDomain).mp restSmooth).2
    have derivativeDifferentiable :=
      (derivativeSmooth.contDiffAt
        (openDomain.mem_nhds inside)).differentiableAt (by simp)
    simp only [operatorCartesianListDerivative, List.foldr_cons]
    change fderiv ℝ (fun source => fderiv ℝ
        (operatorCartesianListDerivative rest function) source
          (spatialBasis first)) point (spatialBasis second) =
      fderiv ℝ (fun source => fderiv ℝ
        (operatorCartesianListDerivative rest function) source
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

theorem cartesianList_canonical_perm (word : List (Fin 2)) :
    word.Perm
      (List.replicate (word.count 0) 0 ++
        List.replicate (word.count 1) 1) := by
  apply List.perm_iff_count.mpr
  intro direction
  fin_cases direction <;> simp [List.count_replicate]

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

theorem smoothOperatorDerivative_eq_of_spec
    {inputDimension outputDimension : ℕ}
    (field : SmoothOperatorJet inputDimension outputDimension)
    (index : CartesianMultiIndex)
    (extension : ContinuousMap ClosedDisk
      (OperatorValue inputDimension outputDimension))
    (specification : IsOperatorDerivativeExtension field.value index extension) :
    smoothOperatorDerivative field index = extension := by
  apply continuousMap_eq_of_openDisk
  intro point inside
  exact (Classical.choose_spec (field.derivativeExists index) point inside).trans
    (specification point inside).symm

def shiftedOperatorIndex (new fixed : CartesianMultiIndex) : CartesianMultiIndex :=
  (new.1 + fixed.1, new.2 + fixed.2)

def shiftedOperatorJetValue {inputDimension outputDimension : ℕ}
    (field : SmoothOperatorJet inputDimension outputDimension)
    (fixed : CartesianMultiIndex) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  smoothOperatorDerivative field fixed

theorem closedDiskLift_shiftedOperatorJetValue_interior
    {inputDimension outputDimension : ℕ}
    (field : SmoothOperatorJet inputDimension outputDimension)
    (fixed : CartesianMultiIndex) (point : SpatialPlane)
    (inside : point ∈ openUnitDisk) :
    closedDiskLift (shiftedOperatorJetValue field fixed) point =
      operatorCartesianListDerivative
        (List.ofFn (cartesianMultiIndexWord fixed))
        (closedDiskLift field.value) point := by
  rw [show closedDiskLift (shiftedOperatorJetValue field fixed) point =
      shiftedOperatorJetValue field fixed
        ⟨point, openDiskMembershipClosed point inside⟩ by
    simp [closedDiskLift, openDiskMembershipClosed point inside]]
  change (Classical.choose (field.derivativeExists fixed))
      ⟨point, openDiskMembershipClosed point inside⟩ = _
  rw [Classical.choose_spec (field.derivativeExists fixed)
    ⟨point, openDiskMembershipClosed point inside⟩ inside]
  exact (operatorCartesianListDerivative_ofFn openUnitDisk_isOpen
    (cartesianOrder fixed) (cartesianMultiIndexWord fixed)
    field.smoothInterior inside).symm

theorem shiftedOperatorJetValue_smoothInterior
    {inputDimension outputDimension : ℕ}
    (field : SmoothOperatorJet inputDimension outputDimension)
    (fixed : CartesianMultiIndex) :
    ContDiffOn ℝ ∞ (closedDiskLift (shiftedOperatorJetValue field fixed))
      openUnitDisk := by
  apply (operatorCartesianListDerivative_smooth openUnitDisk_isOpen
    (List.ofFn (cartesianMultiIndexWord fixed)) field.smoothInterior).congr
  intro point inside
  exact closedDiskLift_shiftedOperatorJetValue_interior field fixed point inside

def shiftedOperatorJetDerivativeValue
    {inputDimension outputDimension : ℕ}
    (field : SmoothOperatorJet inputDimension outputDimension)
    (fixed new : CartesianMultiIndex) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  smoothOperatorDerivative field (shiftedOperatorIndex new fixed)

theorem shiftedOperatorJetDerivativeValue_spec
    {inputDimension outputDimension : ℕ}
    (field : SmoothOperatorJet inputDimension outputDimension)
    (fixed new : CartesianMultiIndex) :
    IsOperatorDerivativeExtension (shiftedOperatorJetValue field fixed) new
      (shiftedOperatorJetDerivativeValue field fixed new) := by
  intro point inside
  change (Classical.choose
      (field.derivativeExists (shiftedOperatorIndex new fixed))) point = _
  rw [Classical.choose_spec
    (field.derivativeExists (shiftedOperatorIndex new fixed)) point inside]
  have localEquality :
      closedDiskLift (shiftedOperatorJetValue field fixed) =ᶠ[𝓝 point.val]
        operatorCartesianListDerivative
          (List.ofFn (cartesianMultiIndexWord fixed))
          (closedDiskLift field.value) := by
    filter_upwards [openUnitDisk_isOpen.mem_nhds inside] with candidate candidateInside
    exact closedDiskLift_shiftedOperatorJetValue_interior
      field fixed candidate candidateInside
  have derivativeEquality :=
    (localEquality.iteratedFDeriv ℝ (cartesianOrder new)).self_of_nhds
  change cartesianDerivative (cartesianOrder (shiftedOperatorIndex new fixed))
      (cartesianMultiIndexWord (shiftedOperatorIndex new fixed))
      (closedDiskLift field.value) point.val =
    cartesianDerivative (cartesianOrder new) (cartesianMultiIndexWord new)
      (closedDiskLift (shiftedOperatorJetValue field fixed)) point.val
  have combinedOrder : cartesianOrder (shiftedOperatorIndex new fixed) =
      cartesianOrder new + cartesianOrder fixed := by
    simp [shiftedOperatorIndex, cartesianOrder]
    omega
  change cartesianDerivative (cartesianOrder (shiftedOperatorIndex new fixed))
      (cartesianMultiIndexWord (shiftedOperatorIndex new fixed))
      (closedDiskLift field.value) point.val =
    (iteratedFDeriv ℝ (cartesianOrder new)
      (closedDiskLift (shiftedOperatorJetValue field fixed)) point.val)
        (fun position => spatialBasis (cartesianMultiIndexWord new position))
  rw [derivativeEquality]
  change cartesianDerivative (cartesianOrder (shiftedOperatorIndex new fixed))
      (cartesianMultiIndexWord (shiftedOperatorIndex new fixed))
      (closedDiskLift field.value) point.val =
    cartesianDerivative (cartesianOrder new) (cartesianMultiIndexWord new)
      (operatorCartesianListDerivative
        (List.ofFn (cartesianMultiIndexWord fixed))
        (closedDiskLift field.value)) point.val
  rw [← operatorCartesianListDerivative_ofFn openUnitDisk_isOpen
    (cartesianOrder (shiftedOperatorIndex new fixed))
    (cartesianMultiIndexWord (shiftedOperatorIndex new fixed))
    field.smoothInterior inside]
  rw [← operatorCartesianListDerivative_ofFn openUnitDisk_isOpen
    (cartesianOrder new) (cartesianMultiIndexWord new)
    (operatorCartesianListDerivative_smooth openUnitDisk_isOpen
      (List.ofFn (cartesianMultiIndexWord fixed)) field.smoothInterior) inside]
  rw [← operatorCartesianListDerivative_append]
  have permuted :
      (List.ofFn (cartesianMultiIndexWord (shiftedOperatorIndex new fixed))).Perm
        (List.ofFn (cartesianMultiIndexWord new) ++
          List.ofFn (cartesianMultiIndexWord fixed)) := by
    rw [list_ofFn_cartesianMultiIndexWord]
    have canonical := (cartesianList_canonical_perm
      (List.ofFn (cartesianMultiIndexWord new) ++
        List.ofFn (cartesianMultiIndexWord fixed))).symm
    simpa [list_ofFn_cartesianMultiIndexWord, shiftedOperatorIndex,
      List.count_append, List.count_replicate] using canonical
  exact operatorCartesianListDerivative_perm openUnitDisk_isOpen permuted
    field.smoothInterior (x := point.val) inside

def shiftedOperatorJet {inputDimension outputDimension : ℕ}
    (field : SmoothOperatorJet inputDimension outputDimension)
    (fixed : CartesianMultiIndex) :
    SmoothOperatorJet inputDimension outputDimension where
  value := shiftedOperatorJetValue field fixed
  smoothInterior := shiftedOperatorJetValue_smoothInterior field fixed
  derivativeExists := fun new =>
    ⟨shiftedOperatorJetDerivativeValue field fixed new,
      shiftedOperatorJetDerivativeValue_spec field fixed new⟩

theorem shiftedOperatorJet_derivative
    {inputDimension outputDimension : ℕ}
    (field : SmoothOperatorJet inputDimension outputDimension)
    (fixed new : CartesianMultiIndex) :
    smoothOperatorDerivative (shiftedOperatorJet field fixed) new =
      smoothOperatorDerivative field (shiftedOperatorIndex new fixed) := by
  exact smoothOperatorDerivative_eq_of_spec _ _ _
    (shiftedOperatorJetDerivativeValue_spec field fixed new)

def operatorJetAddValue {inputDimension outputDimension : ℕ}
    (first second : SmoothOperatorJet inputDimension outputDimension) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  first.value + second.value

theorem closedDiskLift_operatorJetAddValue
    {inputDimension outputDimension : ℕ}
    (first second : SmoothOperatorJet inputDimension outputDimension) :
    closedDiskLift (operatorJetAddValue first second) =
      closedDiskLift first.value + closedDiskLift second.value := by
  funext point
  by_cases membership : point ∈ closedUnitDisk <;>
    simp [closedDiskLift, operatorJetAddValue, membership]

def operatorJetAddDerivativeValue {inputDimension outputDimension : ℕ}
    (first second : SmoothOperatorJet inputDimension outputDimension)
    (index : CartesianMultiIndex) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  smoothOperatorDerivative first index + smoothOperatorDerivative second index

theorem operatorJetAddDerivativeValue_spec
    {inputDimension outputDimension : ℕ}
    (first second : SmoothOperatorJet inputDimension outputDimension)
    (index : CartesianMultiIndex) :
    IsOperatorDerivativeExtension (operatorJetAddValue first second) index
      (operatorJetAddDerivativeValue first second index) := by
  intro point inside
  rw [show operatorJetAddDerivativeValue first second index point =
      smoothOperatorDerivative first index point +
        smoothOperatorDerivative second index point from rfl]
  change (Classical.choose (first.derivativeExists index)) point +
      (Classical.choose (second.derivativeExists index)) point = _
  rw [Classical.choose_spec (first.derivativeExists index) point inside,
    Classical.choose_spec (second.derivativeExists index) point inside]
  rw [closedDiskLift_operatorJetAddValue]
  have firstSmooth : ContDiffAt ℝ (cartesianOrder index)
      (closedDiskLift first.value) point.val :=
    ((first.smoothInterior point.val inside).of_le
      (WithTop.coe_le_coe.mpr (show (cartesianOrder index : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      (openUnitDisk_isOpen.mem_nhds inside)
  have secondSmooth : ContDiffAt ℝ (cartesianOrder index)
      (closedDiskLift second.value) point.val :=
    ((second.smoothInterior point.val inside).of_le
      (WithTop.coe_le_coe.mpr (show (cartesianOrder index : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      (openUnitDisk_isOpen.mem_nhds inside)
  have derivativeIdentity := iteratedFDeriv_add_apply firstSmooth secondSmooth
  exact (congrArg
    (fun derivative => derivative
      (fun position => spatialBasis (cartesianMultiIndexWord index position)))
    derivativeIdentity).symm

def operatorJetAdd {inputDimension outputDimension : ℕ}
    (first second : SmoothOperatorJet inputDimension outputDimension) :
    SmoothOperatorJet inputDimension outputDimension where
  value := operatorJetAddValue first second
  smoothInterior := by
    rw [closedDiskLift_operatorJetAddValue]
    exact first.smoothInterior.add second.smoothInterior
  derivativeExists := fun index =>
    ⟨operatorJetAddDerivativeValue first second index,
      operatorJetAddDerivativeValue_spec first second index⟩

theorem operatorJetAdd_derivative {inputDimension outputDimension : ℕ}
    (first second : SmoothOperatorJet inputDimension outputDimension)
    (index : CartesianMultiIndex) :
    smoothOperatorDerivative (operatorJetAdd first second) index =
      smoothOperatorDerivative first index + smoothOperatorDerivative second index := by
  exact smoothOperatorDerivative_eq_of_spec _ _ _
    (operatorJetAddDerivativeValue_spec first second index)

def laplacianSmoothOperatorJet {inputDimension outputDimension : ℕ}
    (field : SmoothOperatorJet inputDimension outputDimension) :
    SmoothOperatorJet inputDimension outputDimension :=
  operatorJetAdd (shiftedOperatorJet field (2, 0))
    (shiftedOperatorJet field (0, 2))

theorem laplacianSmoothOperatorJet_derivative
    {inputDimension outputDimension : ℕ}
    (field : SmoothOperatorJet inputDimension outputDimension)
    (index : CartesianMultiIndex) :
    smoothOperatorDerivative (laplacianSmoothOperatorJet field) index =
      smoothOperatorDerivative field (index.1 + 2, index.2) +
        smoothOperatorDerivative field (index.1, index.2 + 2) := by
  rw [laplacianSmoothOperatorJet, operatorJetAdd_derivative,
    shiftedOperatorJet_derivative, shiftedOperatorJet_derivative]
  rfl

end Grad.GaugeCoefficients.Radial
