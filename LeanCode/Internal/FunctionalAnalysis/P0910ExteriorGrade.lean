import P0910GradeExtension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section

open Filter Set MeasureTheory
open scoped BigOperators ContDiff ENNReal Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets
open Grad.DiskExtension.Seeley

local instance p0910ExteriorGradeClosedDiskCompactSpace :
    CompactSpace ClosedDisk := by
  rw [← isCompact_iff_compactSpace, closedUnitDisk_eq_closedBall]
  exact isCompact_closedBall (0 : SpatialPlane) 1

local instance p0910ExteriorGradeCellProbabilityFinite :
    IsFiniteMeasure cellProbabilityMeasure := by
  unfold cellProbabilityMeasure
  apply Measure.smul_finite AddCircle.haarAddCircle
  rw [ENNReal.inv_ne_top]
  exact (ENNReal.ofReal_pos.mpr
    (mul_pos (by norm_num) Real.pi_pos)).ne'

def mixedDirectionDerivative {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (direction : Fin 3) (function : SpatialCell → Value) : SpatialCell → Value :=
  fun point => fderiv ℝ function point (spatialCellBasis direction)

def mixedListDerivative {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (word : List (Fin 3)) (function : SpatialCell → Value) : SpatialCell → Value :=
  word.foldr mixedDirectionDerivative function

theorem mixedDirectionDerivative_smooth {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set SpatialCell} (openDomain : IsOpen domain) (direction : Fin 3)
    {function : SpatialCell → Value} (smooth : ContDiffOn ℝ ∞ function domain) :
    ContDiffOn ℝ ∞ (mixedDirectionDerivative direction function) domain :=
  ((contDiffOn_infty_iff_fderiv_of_isOpen openDomain).mp smooth).2.clm_apply
    contDiffOn_const

theorem mixedListDerivative_smooth {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set SpatialCell} (openDomain : IsOpen domain) (word : List (Fin 3))
    {function : SpatialCell → Value} (smooth : ContDiffOn ℝ ∞ function domain) :
    ContDiffOn ℝ ∞ (mixedListDerivative word function) domain := by
  induction word with
  | nil => exact smooth
  | cons direction rest inductionHypothesis =>
      exact mixedDirectionDerivative_smooth openDomain direction inductionHypothesis

theorem mixedDirectionDerivative_congr {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set SpatialCell} (openDomain : IsOpen domain) (direction : Fin 3)
    {first second : SpatialCell → Value} (agree : Set.EqOn first second domain) :
    Set.EqOn (mixedDirectionDerivative direction first)
      (mixedDirectionDerivative direction second) domain := by
  intro point inside
  have localEquality : first =ᶠ[𝓝 point] second :=
    Filter.eventually_of_mem (openDomain.mem_nhds inside) agree
  exact congrArg
    (fun derivative : SpatialCell →L[ℝ] Value =>
      derivative (spatialCellBasis direction)) localEquality.fderiv_eq

theorem mixedDirectionDerivative_commute {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set SpatialCell} (openDomain : IsOpen domain)
    (first second : Fin 3) {function : SpatialCell → Value}
    (smooth : ContDiffOn ℝ ∞ function domain) :
    Set.EqOn
      (mixedDirectionDerivative first (mixedDirectionDerivative second function))
      (mixedDirectionDerivative second (mixedDirectionDerivative first function))
      domain := by
  intro point inside
  have localSmooth := smooth.contDiffAt (openDomain.mem_nhds inside)
  have derivativeSmooth :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen openDomain).mp smooth).2
  have derivativeDifferentiable :=
    (derivativeSmooth.contDiffAt
      (openDomain.mem_nhds inside)).differentiableAt (by simp)
  change fderiv ℝ
      (fun source => fderiv ℝ function source (spatialCellBasis second)) point
        (spatialCellBasis first) =
    fderiv ℝ
      (fun source => fderiv ℝ function source (spatialCellBasis first)) point
        (spatialCellBasis second)
  rw [fderiv_clm_apply derivativeDifferentiable
      (differentiableAt_const (spatialCellBasis second)),
    fderiv_clm_apply derivativeDifferentiable
      (differentiableAt_const (spatialCellBasis first))]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact (localSmooth.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eq _ _

theorem mixedListDerivative_perm {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set SpatialCell} (openDomain : IsOpen domain)
    {first second : List (Fin 3)} (permuted : first.Perm second)
    {function : SpatialCell → Value} (smooth : ContDiffOn ℝ ∞ function domain) :
    Set.EqOn (mixedListDerivative first function)
      (mixedListDerivative second function) domain := by
  induction permuted with
  | nil => exact fun _ _ => rfl
  | cons direction permuted inductionHypothesis =>
      exact mixedDirectionDerivative_congr openDomain direction inductionHypothesis
  | swap first second rest =>
      exact mixedDirectionDerivative_commute openDomain second first
        (mixedListDerivative_smooth openDomain rest smooth)
  | trans first second inductionFirst inductionSecond =>
      exact inductionFirst.trans inductionSecond

theorem mixedListDerivative_ofFn {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set SpatialCell} (openDomain : IsOpen domain)
    (order : ℕ) (word : MixedCartesianWord order)
    {function : SpatialCell → Value} (smooth : ContDiffOn ℝ ∞ function domain) :
    Set.EqOn (mixedListDerivative (List.ofFn word) function)
      (mixedCartesianDerivative order word function) domain := by
  induction order with
  | zero => exact fun _ _ => rfl
  | succ order inductionHypothesis =>
      intro point inside
      rw [List.ofFn_succ]
      have congruence := mixedDirectionDerivative_congr openDomain (word 0)
        (inductionHypothesis (Fin.tail word)) inside
      refine congruence.trans ?_
      have derivativeDifferentiable :=
        (smooth.contDiffAt (openDomain.mem_nhds inside)).differentiableAt_iteratedFDeriv
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl order)
      exact (derivativeDifferentiable.iteratedFDeriv_succ_apply_left'
        (m := fun position => spatialCellBasis (word position))).symm

theorem mixedList_counts (word : List (Fin 3)) :
    word.count 0 + word.count 1 + word.count 2 = word.length := by
  induction word with
  | nil => simp
  | cons direction rest inductionHypothesis =>
      fin_cases direction <;> simp_all <;> omega

def mixedWordMultiIndex {order : ℕ}
    (word : MixedCartesianWord order) : DiskCellMultiIndex :=
  (((List.ofFn word).count 0, (List.ofFn word).count 1),
    (List.ofFn word).count 2)

@[simp] theorem mixedWordMultiIndex_order {order : ℕ}
    (word : MixedCartesianWord order) :
    diskCellOrder (mixedWordMultiIndex word) = order := by
  simpa [mixedWordMultiIndex, diskCellOrder] using
    mixedList_counts (List.ofFn word)

theorem list_ofFn_diskCellMultiIndexWord (index : DiskCellMultiIndex) :
    List.ofFn (diskCellMultiIndexWord index) =
      List.replicate index.1.1 0 ++ List.replicate index.1.2 1 ++
        List.replicate index.2 2 := by
  apply List.ext_get
  · rw [List.length_ofFn, List.length_append, List.length_append,
      List.length_replicate, List.length_replicate, List.length_replicate]
    simp [diskCellOrder, add_assoc]
  · intro position firstBound secondBound
    simp only [List.get_eq_getElem]
    by_cases beforeSecond : position < index.1.1 + index.1.2
    · rw [List.getElem_append_left (by simpa using beforeSecond)]
      by_cases beforeFirst : position < index.1.1
      · rw [List.getElem_append_left (by simpa using beforeFirst)]
        simp [diskCellMultiIndexWord, beforeFirst]
      · rw [List.getElem_append_right (by
            simpa using Nat.le_of_not_gt beforeFirst)]
        simp [diskCellMultiIndexWord, beforeFirst, beforeSecond]
    · rw [List.getElem_append_right (by
          simpa using Nat.le_of_not_gt beforeSecond)]
      have notBeforeFirst : ¬ position < index.1.1 := by omega
      simp [diskCellMultiIndexWord, beforeSecond, notBeforeFirst]

theorem mixedList_canonical_perm (word : List (Fin 3)) :
    word.Perm
      (List.replicate (word.count 0) 0 ++ List.replicate (word.count 1) 1 ++
        List.replicate (word.count 2) 2) := by
  apply List.perm_iff_count.mpr
  intro direction
  fin_cases direction <;> simp [List.count_replicate]

theorem mixedWord_canonical_perm {order : ℕ}
    (word : MixedCartesianWord order) :
    (List.ofFn word).Perm
      (List.ofFn (diskCellMultiIndexWord (mixedWordMultiIndex word))) := by
  rw [list_ofFn_diskCellMultiIndexWord]
  exact mixedList_canonical_perm (List.ofFn word)

theorem closedMixedDerivative_eq_multiIndexDerivative
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) :
    closedMixedDerivative field order word =
      closedDiskCellMultiDerivative field (mixedWordMultiIndex word) := by
  apply continuousMap_eq_of_openDiskCell
  rintro ⟨point, circle⟩ membership
  obtain ⟨cell, rfl⟩ := QuotientAddGroup.mk_surjective circle
  let ambient := assembleSpatialCell point.val cell
  have ambientMembership : ambient ∈ openUnitCylinder := by
    change ‖planarPart ambient‖ < 1
    simpa [ambient, openUnitDisk] using membership
  have pointIdentity :
      diskCellPoint ambient
        (openCylinderMembershipClosed ambient ambientMembership) =
          (point, (cell : CellCircle)) := by
    simpa [ambient] using diskCellPoint_assembleSpatialCell point cell membership
  rw [← pointIdentity]
  rw [closedMixedDerivative_spec field order word ambient ambientMembership]
  rw [closedDiskCellMultiDerivative,
    closedMixedDerivative_spec field
      (diskCellOrder (mixedWordMultiIndex word))
      (diskCellMultiIndexWord (mixedWordMultiIndex word)) ambient ambientMembership]
  calc
    mixedCartesianDerivative order word (diskCellLift field.value) ambient =
        mixedListDerivative (List.ofFn word)
          (diskCellLift field.value) ambient :=
      (mixedListDerivative_ofFn openUnitCylinder_isOpen order word
        field.smoothInterior ambientMembership).symm
    _ = mixedListDerivative
        (List.ofFn (diskCellMultiIndexWord (mixedWordMultiIndex word)))
          (diskCellLift field.value) ambient :=
      mixedListDerivative_perm openUnitCylinder_isOpen
        (mixedWord_canonical_perm word) field.smoothInterior ambientMembership
    _ = mixedCartesianDerivative
        (diskCellOrder (mixedWordMultiIndex word))
        (diskCellMultiIndexWord (mixedWordMultiIndex word))
          (diskCellLift field.value) ambient :=
      mixedListDerivative_ofFn openUnitCylinder_isOpen
        (diskCellOrder (mixedWordMultiIndex word))
        (diskCellMultiIndexWord (mixedWordMultiIndex word))
          field.smoothInterior ambientMembership

def spatialPlaneOfPair (point : ℝ × ℝ) : SpatialPlane :=
  WithLp.toLp 2 ![point.1, point.2]

@[simp] theorem spatialPlaneOfPair_apply_zero (point : ℝ × ℝ) :
    spatialPlaneOfPair point 0 = point.1 := rfl

@[simp] theorem spatialPlaneOfPair_apply_one (point : ℝ × ℝ) :
    spatialPlaneOfPair point 1 = point.2 := rfl

theorem spatialPlaneOfPair_norm_sq (point : ℝ × ℝ) :
    ‖spatialPlaneOfPair point‖ ^ 2 = point.1 ^ 2 + point.2 ^ 2 := by
  rw [PiLp.norm_eq_sum (p := 2) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, one_div]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt]
  · simp [Fin.sum_univ_two, sq_abs]
  · positivity

theorem spatialPlaneOfPair_polar_norm (radius angle : ℝ)
    (radiusNonnegative : 0 ≤ radius) :
    ‖spatialPlaneOfPair (polarCoord.symm (radius, angle))‖ = radius := by
  rw [← sq_eq_sq₀ (norm_nonneg _) radiusNonnegative]
  rw [spatialPlaneOfPair_norm_sq]
  change (radius * Real.cos angle) ^ 2 + (radius * Real.sin angle) ^ 2 =
    radius ^ 2
  nlinarith [Real.sin_sq_add_cos_sq angle]

def spatialPlaneCoordinateMeasurableEquiv : SpatialPlane ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans
    MeasurableEquiv.finTwoArrow

theorem spatialPlaneCoordinateMeasurableEquiv_symm (point : ℝ × ℝ) :
    spatialPlaneCoordinateMeasurableEquiv.symm point = spatialPlaneOfPair point := by
  rfl

theorem spatialPlaneOfPair_coordinateEquiv (point : SpatialPlane) :
    spatialPlaneOfPair (spatialPlaneCoordinateMeasurableEquiv point) = point := by
  ext coordinate
  fin_cases coordinate <;> rfl

theorem spatialPlaneCoordinate_measurePreserving :
    MeasurePreserving spatialPlaneCoordinateMeasurableEquiv
      (volume : Measure SpatialPlane) ((volume : Measure ℝ).prod volume) := by
  exact (volume_preserving_finTwoArrow ℝ).comp
    (PiLp.volume_preserving_ofLp (Fin 2))

theorem continuous_spatialPlaneOfPair : Continuous spatialPlaneOfPair := by
  exact spatialPlaneCoordinateHomeomorph.symm.continuous

theorem integral_spatialPlane_eq_pair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : SpatialPlane → E) :
    (∫ point : SpatialPlane, function point) =
      ∫ point : ℝ × ℝ, function (spatialPlaneOfPair point)
        ∂((volume : Measure ℝ).prod volume) := by
  have transformed := spatialPlaneCoordinate_measurePreserving.integral_comp'
    (fun point : ℝ × ℝ =>
      function (spatialPlaneCoordinateMeasurableEquiv.symm point))
  simpa only [spatialPlaneCoordinateMeasurableEquiv_symm,
    spatialPlaneOfPair_coordinateEquiv] using transformed

theorem integral_spatialPlane_eq_polar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : SpatialPlane → E) :
    (∫ point : SpatialPlane, function point) =
      ∫ point : ℝ × ℝ in polarCoord.target,
        point.1 • function (spatialPlaneOfPair (polarCoord.symm point)) := by
  rw [integral_spatialPlane_eq_pair]
  exact (integral_comp_polarCoord_symm
    (fun point : ℝ × ℝ => function (spatialPlaneOfPair point))).symm

theorem reflectedPoint_polar
    (index : ℕ) (radius angle : ℝ) (radiusPositive : 0 < radius) :
    reflectedPoint index
        (spatialPlaneOfPair (polarCoord.symm (radius, angle))) =
      spatialPlaneOfPair (polarCoord.symm
        (1 + node index - node index * radius, angle)) := by
  have normIdentity := spatialPlaneOfPair_polar_norm radius angle radiusPositive.le
  rw [reflectedPoint, normIdentity]
  ext coordinate
  fin_cases coordinate <;>
    simp [spatialPlaneOfPair, polarCoord, radiusPositive.ne'] <;>
    ring_nf <;> simp

def exteriorSupportUpperRadius (index : ℕ) : ℝ :=
  1 + cutoffSupportWidth / node index

theorem exteriorSupportUpperRadius_gt_one (index : ℕ) :
    1 < exteriorSupportUpperRadius index := by
  unfold exteriorSupportUpperRadius
  rw [collar_constants.2.2.1]
  exact lt_add_of_pos_right 1 (div_pos (by norm_num) (node_positive index))

theorem radial_reflection_integral_le
    (index : ℕ) (function : ℝ → ℝ)
    (continuousFunction : Continuous function)
    (functionNonnegative : ∀ radius, 0 ≤ function radius) :
    (∫ radius in (1 : ℝ)..exteriorSupportUpperRadius index,
        radius * function (1 + node index - node index * radius)) ≤
      (7 / (5 * node index)) *
        ∫ radius in (0 : ℝ)..1, radius * function radius := by
  let sourceFunction : ℝ → ℝ := fun radius =>
    ((1 + node index - radius) / node index) * function radius
  have nodePositive : 0 < node index := node_positive index
  have sourceContinuous : Continuous sourceFunction := by
    dsimp only [sourceFunction]
    fun_prop
  have substitution := intervalIntegral.integral_comp_sub_mul
    (a := (1 : ℝ)) (b := exteriorSupportUpperRadius index)
    sourceFunction nodePositive.ne' (1 + node index)
  have lowerEndpoint :
      1 + node index - node index * exteriorSupportUpperRadius index =
        (5 / 6 : ℝ) := by
    rw [exteriorSupportUpperRadius, collar_constants.2.2.1]
    field_simp [nodePositive.ne']
    ring
  have upperEndpoint :
      1 + node index - node index * (1 : ℝ) = 1 := by ring
  have integrandEquality :
      (fun radius => sourceFunction
        (1 + node index - node index * radius)) =
      (fun radius => radius *
        function (1 + node index - node index * radius)) := by
    funext radius
    dsimp only [sourceFunction]
    field_simp [nodePositive.ne']
    ring
  rw [integrandEquality, lowerEndpoint, upperEndpoint] at substitution
  rw [substitution]
  have sourceIntervalIntegrable : IntervalIntegrable sourceFunction volume
      (5 / 6 : ℝ) 1 :=
    sourceContinuous.intervalIntegrable _ _
  let comparisonFunction : ℝ → ℝ := fun radius =>
    (7 / 5 : ℝ) * (radius * function radius)
  have comparisonContinuous : Continuous comparisonFunction := by
    dsimp only [comparisonFunction]
    fun_prop
  have pointwiseComparison : ∀ radius ∈ Set.Icc (5 / 6 : ℝ) 1,
      sourceFunction radius ≤ comparisonFunction radius := by
    intro radius membership
    dsimp only [sourceFunction, comparisonFunction]
    have radiusNonnegative : 0 ≤ radius := by linarith [membership.1]
    have functionValueNonnegative := functionNonnegative radius
    have nodeOne : 1 ≤ node index := node_one_le index
    have affineBound :
        (1 + node index - radius) / node index ≤ (7 / 5 : ℝ) * radius := by
      apply (div_le_iff₀ nodePositive).2
      nlinarith [membership.1, membership.2]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right affineBound functionValueNonnegative
  have comparisonIntervalIntegrable : IntervalIntegrable comparisonFunction volume
      (5 / 6 : ℝ) 1 := comparisonContinuous.intervalIntegrable _ _
  have intervalComparison :
      (∫ radius in (5 / 6 : ℝ)..1, sourceFunction radius) ≤
        ∫ radius in (5 / 6 : ℝ)..1, comparisonFunction radius :=
    intervalIntegral.integral_mono_on (by norm_num)
      sourceIntervalIntegrable comparisonIntervalIntegrable pointwiseComparison
  have baseContinuous : Continuous (fun radius => radius * function radius) := by
    fun_prop
  have baseIntervalIntegrable : IntervalIntegrable
      (fun radius => radius * function radius) volume (0 : ℝ) 1 :=
    baseContinuous.intervalIntegrable _ _
  have baseNonnegative :
      0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
        (fun radius => radius * function radius) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius membership
    exact mul_nonneg membership.1.le (functionNonnegative radius)
  have subintervalComparison :
      (∫ radius in (5 / 6 : ℝ)..1, radius * function radius) ≤
        ∫ radius in (0 : ℝ)..1, radius * function radius := by
    exact intervalIntegral.integral_mono_interval (by norm_num) (by norm_num)
      le_rfl baseNonnegative baseIntervalIntegrable
  rw [show (∫ radius in (5 / 6 : ℝ)..1, comparisonFunction radius) =
      (7 / 5 : ℝ) *
        ∫ radius in (5 / 6 : ℝ)..1, radius * function radius by
    simp [comparisonFunction]] at intervalComparison
  calc
    (node index)⁻¹ *
        ∫ radius in (5 / 6 : ℝ)..1, sourceFunction radius ≤
      (node index)⁻¹ * ((7 / 5 : ℝ) *
        ∫ radius in (5 / 6 : ℝ)..1, radius * function radius) :=
      mul_le_mul_of_nonneg_left intervalComparison (inv_nonneg.mpr nodePositive.le)
    _ ≤ (node index)⁻¹ * ((7 / 5 : ℝ) *
        ∫ radius in (0 : ℝ)..1, radius * function radius) := by
      gcongr
    _ = (7 / (5 * node index)) *
        ∫ radius in (0 : ℝ)..1, radius * function radius := by
      field_simp [nodePositive.ne']

def exteriorSupportAnnulus (index : ℕ) : Set SpatialPlane :=
  {point | 1 < ‖point‖ ∧
    node index * (‖point‖ - 1) < cutoffSupportWidth}

theorem exteriorSupportAnnulus_measurable (index : ℕ) :
    MeasurableSet (exteriorSupportAnnulus index) := by
  have normContinuous : Continuous (fun point : SpatialPlane => ‖point‖) :=
    continuous_norm
  exact ((isOpen_lt (continuous_const : Continuous
      (fun _ : SpatialPlane => (1 : ℝ))) normContinuous).inter
    (isOpen_lt
      ((normContinuous.sub (continuous_const : Continuous
        (fun _ : SpatialPlane => (1 : ℝ)))).const_mul (node index))
      (continuous_const : Continuous
        (fun _ : SpatialPlane => cutoffSupportWidth)))).measurableSet

theorem spatialPlaneOfPair_polar_mem_exteriorSupportAnnulus
    (index : ℕ) (radius angle : ℝ) (radiusPositive : 0 < radius) :
    spatialPlaneOfPair (polarCoord.symm (radius, angle)) ∈
        exteriorSupportAnnulus index ↔
      radius ∈ Set.Ioo (1 : ℝ) (exteriorSupportUpperRadius index) := by
  change (1 < ‖spatialPlaneOfPair (polarCoord.symm (radius, angle))‖ ∧
    node index *
      (‖spatialPlaneOfPair (polarCoord.symm (radius, angle))‖ - 1) <
        cutoffSupportWidth) ↔ _
  rw [spatialPlaneOfPair_polar_norm radius angle radiusPositive.le]
  change 1 < radius ∧ node index * (radius - 1) < cutoffSupportWidth ↔
    1 < radius ∧ radius < 1 + cutoffSupportWidth / node index
  constructor
  · intro membership
    refine ⟨membership.1, ?_⟩
    have divided : radius - 1 < cutoffSupportWidth / node index :=
      (lt_div_iff₀ (node_positive index)).2 (by
        simpa only [mul_comm] using membership.2)
    linarith
  · intro membership
    refine ⟨membership.1, ?_⟩
    have divided : radius - 1 < cutoffSupportWidth / node index := by
      linarith [membership.2]
    simpa only [mul_comm] using
      (lt_div_iff₀ (node_positive index)).1 divided

theorem exteriorSupportAnnulus_polar_integral
    (index : ℕ) (function : SpatialPlane → ℝ)
    (continuousFunction : Continuous function) :
    (∫ point in exteriorSupportAnnulus index,
        function (reflectedPoint index point)) =
      ∫ angle in Set.Ioo (-Real.pi) Real.pi,
        ∫ radius in (1 : ℝ)..exteriorSupportUpperRadius index,
          radius * function (spatialPlaneOfPair (polarCoord.symm
            (1 + node index - node index * radius, angle))) := by
  let polarIntegrand : ℝ × ℝ → ℝ := fun point =>
    point.1 * function (spatialPlaneOfPair (polarCoord.symm
      (1 + node index - node index * point.1, point.2)))
  have polarIntegrandContinuous : Continuous polarIntegrand := by
    dsimp only [polarIntegrand]
    exact continuous_fst.mul (continuousFunction.comp
      (continuous_spatialPlaneOfPair.comp
        (continuous_polarCoord_symm.comp
          (((continuous_const.add continuous_const).sub
            (continuous_const.mul continuous_fst)).prodMk continuous_snd))))
  have radialUpper : 1 < exteriorSupportUpperRadius index :=
    exteriorSupportUpperRadius_gt_one index
  have compactIntegrable : IntegrableOn polarIntegrand
      (Set.Icc (1 : ℝ) (exteriorSupportUpperRadius index) ×ˢ
        Set.Icc (-Real.pi) Real.pi)
      ((volume : Measure ℝ).prod volume) :=
    polarIntegrandContinuous.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have productIntegrable : IntegrableOn polarIntegrand
      (Set.Ioo (1 : ℝ) (exteriorSupportUpperRadius index) ×ˢ
        Set.Ioo (-Real.pi) Real.pi)
      ((volume : Measure ℝ).prod volume) :=
    compactIntegrable.mono_set (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  rw [← integral_indicator (exteriorSupportAnnulus_measurable index),
    integral_spatialPlane_eq_polar]
  have indicatorEquality :
      polarCoord.target.indicator (fun point : ℝ × ℝ =>
        point.1 • (exteriorSupportAnnulus index).indicator
          (fun spatialPoint => function (reflectedPoint index spatialPoint))
          (spatialPlaneOfPair (polarCoord.symm point))) =
      (Set.Ioo (1 : ℝ) (exteriorSupportUpperRadius index) ×ˢ
        Set.Ioo (-Real.pi) Real.pi).indicator polarIntegrand := by
    funext point
    by_cases targetMembership : point ∈ polarCoord.target
    · have radiusPositive : 0 < point.1 := targetMembership.1
      have angleMembership : point.2 ∈ Set.Ioo (-Real.pi) Real.pi :=
        targetMembership.2
      have annulusMembership :=
        spatialPlaneOfPair_polar_mem_exteriorSupportAnnulus
          index point.1 point.2 radiusPositive
      by_cases radialMembership :
          point.1 ∈ Set.Ioo (1 : ℝ) (exteriorSupportUpperRadius index)
      · rw [Set.indicator_of_mem targetMembership,
          Set.indicator_of_mem (annulusMembership.mpr radialMembership),
          Set.indicator_of_mem (show point ∈
            Set.Ioo (1 : ℝ) (exteriorSupportUpperRadius index) ×ˢ
              Set.Ioo (-Real.pi) Real.pi from
            ⟨radialMembership, angleMembership⟩)]
        rw [reflectedPoint_polar index point.1 point.2 radiusPositive]
        rfl
      · have notAnnulus : spatialPlaneOfPair (polarCoord.symm point) ∉
            exteriorSupportAnnulus index :=
          (not_congr annulusMembership).2 radialMembership
        have notProduct : point ∉
            Set.Ioo (1 : ℝ) (exteriorSupportUpperRadius index) ×ˢ
              Set.Ioo (-Real.pi) Real.pi :=
          fun membership => radialMembership membership.1
        simp only [Set.indicator, if_pos targetMembership,
          if_neg notAnnulus, if_neg notProduct, smul_zero]
    · have notProduct : point ∉
          Set.Ioo (1 : ℝ) (exteriorSupportUpperRadius index) ×ˢ
            Set.Ioo (-Real.pi) Real.pi := by
        intro membership
        apply targetMembership
        exact ⟨lt_trans zero_lt_one membership.1.1, membership.2⟩
      simp only [Set.indicator, if_neg targetMembership,
        if_neg notProduct]
  rw [← integral_indicator polarCoord.open_target.measurableSet,
    indicatorEquality,
    integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  have reversedFubini :
      (∫ point in
          Set.Ioo (1 : ℝ) (exteriorSupportUpperRadius index) ×ˢ
            Set.Ioo (-Real.pi) Real.pi,
          polarIntegrand point ∂((volume : Measure ℝ).prod volume)) =
        ∫ angle in Set.Ioo (-Real.pi) Real.pi,
          ∫ radius in Set.Ioo (1 : ℝ) (exteriorSupportUpperRadius index),
            polarIntegrand (radius, angle) := by
    have restrictedIntegrable : Integrable polarIntegrand
        ((volume.restrict
          (Set.Ioo (1 : ℝ) (exteriorSupportUpperRadius index))).prod
          (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
      rw [Measure.prod_restrict]
      exact productIntegrable
    rw [← Measure.prod_restrict]
    exact integral_prod_symm polarIntegrand restrictedIntegrable
  change (∫ point in
      Set.Ioo (1 : ℝ) (exteriorSupportUpperRadius index) ×ˢ
        Set.Ioo (-Real.pi) Real.pi,
      polarIntegrand point ∂((volume : Measure ℝ).prod volume)) = _
  rw [reversedFubini]
  apply integral_congr_ae
  filter_upwards [] with angle
  rw [intervalIntegral.integral_of_le radialUpper.le,
    Measure.restrict_congr_set Ioo_ae_eq_Ioc]

theorem closedUnitDisk_polar_integral
    (function : SpatialPlane → ℝ) (continuousFunction : Continuous function) :
    (∫ point in closedUnitDisk, function point) =
      ∫ angle in Set.Ioo (-Real.pi) Real.pi,
        ∫ radius in (0 : ℝ)..1,
          radius * function
            (spatialPlaneOfPair (polarCoord.symm (radius, angle))) := by
  let polarIntegrand : ℝ × ℝ → ℝ := fun point =>
    point.1 * function (spatialPlaneOfPair (polarCoord.symm point))
  have polarIntegrandContinuous : Continuous polarIntegrand := by
    dsimp only [polarIntegrand]
    exact continuous_fst.mul (continuousFunction.comp
      (continuous_spatialPlaneOfPair.comp continuous_polarCoord_symm))
  have compactIntegrable : IntegrableOn polarIntegrand
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-Real.pi) Real.pi)
      ((volume : Measure ℝ).prod volume) :=
    polarIntegrandContinuous.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have productIntegrable : IntegrableOn polarIntegrand
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
      ((volume : Measure ℝ).prod volume) :=
    compactIntegrable.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self)
  rw [← integral_indicator (by
      rw [closedUnitDisk_eq_closedBall]
      exact Metric.isClosed_closedBall.measurableSet),
    integral_spatialPlane_eq_polar]
  have indicatorEquality :
      polarCoord.target.indicator (fun point : ℝ × ℝ =>
        point.1 • closedUnitDisk.indicator function
          (spatialPlaneOfPair (polarCoord.symm point))) =
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
        polarIntegrand := by
    funext point
    by_cases targetMembership : point ∈ polarCoord.target
    · have radiusPositive : 0 < point.1 := targetMembership.1
      have angleMembership : point.2 ∈ Set.Ioo (-Real.pi) Real.pi :=
        targetMembership.2
      have normIdentity := spatialPlaneOfPair_polar_norm
        point.1 point.2 radiusPositive.le
      by_cases radiusUpper : point.1 ≤ 1
      · have diskMembership :
            spatialPlaneOfPair (polarCoord.symm point) ∈ closedUnitDisk := by
          change ‖spatialPlaneOfPair (polarCoord.symm point)‖ ≤ 1
          rw [normIdentity]
          exact radiusUpper
        have productMembership : point ∈
            Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi :=
          ⟨⟨radiusPositive, radiusUpper⟩, angleMembership⟩
        simp only [Set.indicator, if_pos targetMembership,
          if_pos diskMembership, if_pos productMembership]
        rfl
      · have diskNonmembership :
            spatialPlaneOfPair (polarCoord.symm point) ∉ closedUnitDisk := by
          change ¬ ‖spatialPlaneOfPair (polarCoord.symm point)‖ ≤ 1
          rwa [normIdentity]
        have productNonmembership : point ∉
            Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi :=
          fun membership => radiusUpper membership.1.2
        simp only [Set.indicator, if_pos targetMembership,
          if_neg diskNonmembership, if_neg productNonmembership, smul_zero]
    · have productNonmembership : point ∉
          Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi := by
        intro membership
        exact targetMembership ⟨membership.1.1, membership.2⟩
      simp only [Set.indicator, if_neg targetMembership,
        if_neg productNonmembership]
  rw [← integral_indicator polarCoord.open_target.measurableSet,
    indicatorEquality,
    integral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]
  change (∫ point in
      Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi,
      polarIntegrand point ∂((volume : Measure ℝ).prod volume)) = _
  have restrictedIntegrable : Integrable polarIntegrand
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact productIntegrable
  rw [← Measure.prod_restrict]
  rw [integral_prod_symm polarIntegrand restrictedIntegrable]
  apply integral_congr_ae
  filter_upwards [] with angle
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

theorem exteriorSupportAnnulus_reflected_integral_le
    (index : ℕ) (function : SpatialPlane → ℝ)
    (continuousFunction : Continuous function)
    (functionNonnegative : ∀ point, 0 ≤ function point) :
    (∫ point in exteriorSupportAnnulus index,
        function (reflectedPoint index point)) ≤
      (7 / (5 * node index)) *
        ∫ point in closedUnitDisk, function point := by
  rw [exteriorSupportAnnulus_polar_integral index function continuousFunction,
    closedUnitDisk_polar_integral function continuousFunction,
    ← integral_const_mul]
  let exteriorRay : ℝ × ℝ → ℝ := fun point =>
    point.1 * function (spatialPlaneOfPair (polarCoord.symm
      (1 + node index - node index * point.1, point.2)))
  let diskRay : ℝ × ℝ → ℝ := fun point =>
    point.1 * function (spatialPlaneOfPair (polarCoord.symm point))
  have exteriorRayContinuous : Continuous exteriorRay := by
    dsimp only [exteriorRay]
    exact continuous_fst.mul (continuousFunction.comp
      (continuous_spatialPlaneOfPair.comp
        (continuous_polarCoord_symm.comp
          (((continuous_const.add continuous_const).sub
            (continuous_const.mul continuous_fst)).prodMk continuous_snd))))
  have diskRayContinuous : Continuous diskRay := by
    dsimp only [diskRay]
    exact continuous_fst.mul (continuousFunction.comp
      (continuous_spatialPlaneOfPair.comp continuous_polarCoord_symm))
  have exteriorJointIntegrable : Integrable exteriorRay
      ((volume.restrict
        (Set.Ioc (1 : ℝ) (exteriorSupportUpperRadius index))).prod
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact (exteriorRayContinuous.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self)
  have diskJointIntegrable : Integrable diskRay
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact (diskRayContinuous.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self)
  have exteriorIteratedIntegrable : Integrable
      (fun angle => ∫ radius in (1 : ℝ)..exteriorSupportUpperRadius index,
        exteriorRay (radius, angle))
      (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) := by
    simpa only [intervalIntegral.integral_of_le
      (exteriorSupportUpperRadius_gt_one index).le] using
        exteriorJointIntegrable.integral_prod_right
  have diskIteratedIntegrable : Integrable
      (fun angle => ∫ radius in (0 : ℝ)..1, diskRay (radius, angle))
      (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      diskJointIntegrable.integral_prod_right
  apply integral_mono exteriorIteratedIntegrable
    (diskIteratedIntegrable.const_mul (7 / (5 * node index)))
  intro angle
  exact radial_reflection_integral_le index
    (fun radius => function
      (spatialPlaneOfPair (polarCoord.symm (radius, angle))))
    (continuousFunction.comp
      (continuous_spatialPlaneOfPair.comp
        (continuous_polarCoord_symm.comp
          (continuous_id.prodMk continuous_const))))
    (fun radius => functionNonnegative _)

noncomputable def closedHigherDerivativePointBound {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) : ℝ :=
  ∑ word : MixedCartesianWord order,
    ‖spatialCellWordCoefficient word‖ *
      ‖closedMixedDerivative field order word (retractedDiskCell point)‖

theorem closedHigherDerivativePointBound_nonnegative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) :
    0 ≤ closedHigherDerivativePointBound field order point := by
  unfold closedHigherDerivativePointBound
  positivity

theorem closedHigherDerivative_norm_le_pointBound {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) :
    ‖closedHigherDerivative (order := order) field point‖ ≤
      closedHigherDerivativePointBound field order point := by
  rw [closedHigherDerivative, closedHigherDerivativePointBound]
  calc
    ‖∑ word : MixedCartesianWord order,
        (spatialCellWordCoefficient word).smulRight
          (closedMixedDerivative field order word (retractedDiskCell point))‖ ≤
      ∑ word : MixedCartesianWord order,
        ‖(spatialCellWordCoefficient word).smulRight
          (closedMixedDerivative field order word (retractedDiskCell point))‖ :=
      norm_sum_le _ _
    _ = ∑ word : MixedCartesianWord order,
        ‖spatialCellWordCoefficient word‖ *
          ‖closedMixedDerivative field order word (retractedDiskCell point)‖ := by
      apply Finset.sum_congr rfl
      intro word _
      exact ContinuousMultilinearMap.norm_smulRight _ _

theorem reflectedSpatialCell_iteratedFDeriv_norm_le_point
    (order index : ℕ) (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    ‖iteratedFDeriv ℝ order (reflectedSpatialCell index) point‖ ≤
      reflectionJetBound order point * node index := by
  rw [iteratedFDeriv_reflectedSpatialCell order index point nonzero]
  have nodeOne : 1 ≤ node index := node_one_le index
  calc
    ‖(1 + node index) • iteratedFDeriv ℝ order normalizedSpatialCell point -
        node index • iteratedFDeriv ℝ order id point‖ ≤
      ‖(1 + node index) • iteratedFDeriv ℝ order normalizedSpatialCell point‖ +
        ‖node index • iteratedFDeriv ℝ order id point‖ := norm_sub_le _ _
    _ = (1 + node index) *
          ‖iteratedFDeriv ℝ order normalizedSpatialCell point‖ +
        node index * ‖iteratedFDeriv ℝ order id point‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < 1 + node index),
        abs_of_pos (node_positive index)]
    _ ≤ (2 * (‖iteratedFDeriv ℝ order normalizedSpatialCell point‖ + 1) +
          (‖iteratedFDeriv ℝ order id point‖ + 1)) * node index := by
      nlinarith [norm_nonneg
          (iteratedFDeriv ℝ order normalizedSpatialCell point),
        norm_nonneg
          (iteratedFDeriv ℝ order (id : SpatialCell → SpatialCell) point)]
    _ = reflectionJetBound order point * node index := rfl

noncomputable def reflectedCompositePointBound {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index order : ℕ)
    (point : SpatialCell) : ℝ :=
  ∑ partition : OrderedFinpartition order,
    closedHigherDerivativePointBound field partition.length
        (reflectedSpatialCell index point) *
      ∏ position : Fin partition.length,
        reflectionJetBound (partition.partSize position) point

theorem reflectedCompositePointBound_nonnegative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index order : ℕ)
    (point : SpatialCell) :
    0 ≤ reflectedCompositePointBound field index order point := by
  unfold reflectedCompositePointBound
  apply Finset.sum_nonneg
  intro partition _
  exact mul_nonneg
    (closedHigherDerivativePointBound_nonnegative field _ _)
    (Finset.prod_nonneg fun position _ =>
      reflectionJetBound_nonnegative (partition.partSize position) point)

theorem reflectedCompositeTaylorSeries_norm_le_point
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (index order : ℕ) (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    ‖reflectedCompositeTaylorSeries field index point order‖ ≤
      reflectedCompositePointBound field index order point *
        node index ^ order := by
  rw [reflectedCompositeTaylorSeries, FormalMultilinearSeries.taylorComp]
  calc
    ‖∑ partition : OrderedFinpartition order,
        (closedTaylorSeries field
          (reflectedSpatialCell index point)).compAlongOrderedFinpartition
            (ftaylorSeries ℝ (reflectedSpatialCell index) point) partition‖ ≤
      ∑ partition : OrderedFinpartition order,
        ‖(closedTaylorSeries field
          (reflectedSpatialCell index point)).compAlongOrderedFinpartition
            (ftaylorSeries ℝ (reflectedSpatialCell index) point) partition‖ :=
      norm_sum_le _ _
    _ ≤ ∑ partition : OrderedFinpartition order,
        (closedHigherDerivativePointBound field partition.length
            (reflectedSpatialCell index point) *
          ∏ position : Fin partition.length,
            reflectionJetBound (partition.partSize position) point) *
          node index ^ order := by
      apply Finset.sum_le_sum
      intro partition _
      calc
        ‖(closedTaylorSeries field
            (reflectedSpatialCell index point)).compAlongOrderedFinpartition
              (ftaylorSeries ℝ (reflectedSpatialCell index) point) partition‖ ≤
          ‖closedTaylorSeries field (reflectedSpatialCell index point)
              partition.length‖ *
            ∏ position : Fin partition.length,
              ‖ftaylorSeries ℝ (reflectedSpatialCell index) point
                (partition.partSize position)‖ :=
          partition.norm_compAlongOrderedFinpartition_le _ _
        _ ≤ closedHigherDerivativePointBound field partition.length
              (reflectedSpatialCell index point) *
            ∏ position : Fin partition.length,
              (reflectionJetBound (partition.partSize position) point *
                node index) := by
          apply mul_le_mul
          · exact closedHigherDerivative_norm_le_pointBound field _ _
          · apply Finset.prod_le_prod
            · intro position _
              positivity
            · intro position _
              exact reflectedSpatialCell_iteratedFDeriv_norm_le_point
                (partition.partSize position) index point nonzero
          · positivity
          · exact closedHigherDerivativePointBound_nonnegative field _ _
        _ = (closedHigherDerivativePointBound field partition.length
              (reflectedSpatialCell index point) *
            ∏ position : Fin partition.length,
              reflectionJetBound (partition.partSize position) point) *
            node index ^ partition.length := by
          rw [Finset.prod_mul_distrib]
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          ring
        _ ≤ (closedHigherDerivativePointBound field partition.length
              (reflectedSpatialCell index point) *
            ∏ position : Fin partition.length,
              reflectionJetBound (partition.partSize position) point) *
            node index ^ order := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (node_one_le index)
              (OrderedFinpartition.length_le partition))
            (mul_nonneg
              (closedHigherDerivativePointBound_nonnegative field _ _)
              (Finset.prod_nonneg fun position _ =>
                reflectionJetBound_nonnegative
                  (partition.partSize position) point))
    _ = reflectedCompositePointBound field index order point *
          node index ^ order := by
      rw [reflectedCompositePointBound, Finset.sum_mul]

theorem cutoffComposite_iteratedFDeriv_norm_le_point
    (order index : ℕ) (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    ‖iteratedFDeriv ℝ order
        (plateauCutoff ∘ exteriorCutoffScale index) point‖ ≤
      cutoffCompositeJetBound order point * node index ^ order := by
  have outerBounds : ∀ derivativeOrder, derivativeOrder ≤ order →
      ‖iteratedFDerivWithin ℝ derivativeOrder plateauCutoff Set.univ
        (exteriorCutoffScale index point)‖ ≤ plateauJetEnvelope order := by
    intro derivativeOrder upper
    rw [iteratedFDerivWithin_univ]
    exact plateauCutoff_iteratedFDeriv_norm_le_envelope
      order derivativeOrder upper _
  have innerBounds : ∀ derivativeOrder, 1 ≤ derivativeOrder →
      derivativeOrder ≤ order →
      ‖iteratedFDerivWithin ℝ derivativeOrder (exteriorCutoffScale index)
        planarNonzeroRegion point‖ ≤
        (radialJetEnvelope order point * node index) ^ derivativeOrder := by
    intro derivativeOrder positive upper
    rw [iteratedFDerivWithin_of_isOpen derivativeOrder
      planarNonzeroRegion_isOpen nonzero]
    change ‖iteratedFDeriv ℝ derivativeOrder
      (fun point => node index • radialOffset point) point‖ ≤ _
    have radialSmooth : ContDiffAt ℝ derivativeOrder radialOffset point :=
      (radialOffset_contDiffAt point nonzero).of_le
        (WithTop.coe_le_coe.mpr
          (show (derivativeOrder : ℕ∞) ≤ ⊤ from le_top))
    rw [iteratedFDeriv_const_smul_apply' radialSmooth, norm_smul,
      Real.norm_eq_abs, abs_of_pos (node_positive index)]
    have derivativeBound :
        ‖iteratedFDeriv ℝ derivativeOrder radialOffset point‖ ≤
          radialJetEnvelope order point := by
      have envelopeBound := radialJet_le_envelope point positive upper
      linarith
    have baseOne : 1 ≤ radialJetEnvelope order point * node index := by
      simpa only [one_mul] using
        mul_le_mul (radialJetEnvelope_one_le order point)
          (node_one_le index) zero_le_one
          (zero_le_one.trans (radialJetEnvelope_one_le order point))
    calc
      node index * ‖iteratedFDeriv ℝ derivativeOrder radialOffset point‖ ≤
          node index * radialJetEnvelope order point :=
        mul_le_mul_of_nonneg_left derivativeBound (node_positive index).le
      _ = radialJetEnvelope order point * node index := mul_comm _ _
      _ ≤ (radialJetEnvelope order point * node index) ^ derivativeOrder := by
        simpa only [pow_one] using
          pow_le_pow_right₀ baseOne positive
  have compositionBound := norm_iteratedFDerivWithin_comp_le
    (𝕜 := ℝ) (n := order) (N := ∞)
    (s := planarNonzeroRegion) (t := Set.univ)
    plateauCutoff_smooth.contDiffOn
    (exteriorCutoffScale_contDiffOn_planarNonzeroRegion index)
    (show (order : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by
      exact WithTop.coe_le_coe.mpr
        (show (order : ℕ∞) ≤ ⊤ from le_top))
    uniqueDiffOn_univ planarNonzeroRegion_isOpen.uniqueDiffOn
    (mapsTo_univ _ _) nonzero
    (C := plateauJetEnvelope order)
    (D := radialJetEnvelope order point * node index)
    outerBounds innerBounds
  have withinEquality := iteratedFDerivWithin_of_isOpen
    (𝕜 := ℝ) (f := plateauCutoff ∘ exteriorCutoffScale index)
    order planarNonzeroRegion_isOpen nonzero
  calc
    ‖iteratedFDeriv ℝ order
        (plateauCutoff ∘ exteriorCutoffScale index) point‖ ≤
      order.factorial * plateauJetEnvelope order *
        (radialJetEnvelope order point * node index) ^ order := by
      rw [← withinEquality]
      exact compositionBound
    _ = cutoffCompositeJetBound order point * node index ^ order := by
      rw [mul_pow]
      unfold cutoffCompositeJetBound
      ring

theorem exteriorScalar_iteratedFDeriv_norm_le_point
    (order index : ℕ) (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    ‖iteratedFDeriv ℝ order (exteriorScalar index) point‖ ≤
      exteriorScalarJetBound order point *
        (|coefficient index| * node index ^ order) := by
  have scaleSmooth : ContDiffAt ℝ ∞ (exteriorCutoffScale index) point :=
    ((radialOffset_contDiffAt point nonzero).const_smul (node index))
  have cutoffSmooth : ContDiffAt ℝ ∞
      (plateauCutoff ∘ exteriorCutoffScale index) point :=
    plateauCutoff_smooth.contDiffAt.comp point scaleSmooth
  have realSmooth : ContDiffAt ℝ ∞
      (fun candidate => coefficient index •
        (plateauCutoff ∘ exteriorCutoffScale index) candidate) point :=
    cutoffSmooth.const_smul (coefficient index)
  have functionEquality : exteriorScalar index =
      Complex.ofRealCLM ∘ (fun candidate => coefficient index •
        (plateauCutoff ∘ exteriorCutoffScale index) candidate) := by
    funext other
    simp [exteriorScalar, exteriorCutoffScale, radialOffset,
      Function.comp_apply]
  rw [functionEquality]
  have linearBound := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left
    realSmooth
    (show (order : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by
      exact WithTop.coe_le_coe.mpr
        (show (order : ℕ∞) ≤ ⊤ from le_top))
  calc
    ‖iteratedFDeriv ℝ order
        (Complex.ofRealCLM ∘ fun candidate => coefficient index •
          (plateauCutoff ∘ exteriorCutoffScale index) candidate) point‖ ≤
      ‖Complex.ofRealCLM‖ *
        ‖iteratedFDeriv ℝ order (fun candidate => coefficient index •
          (plateauCutoff ∘ exteriorCutoffScale index) candidate) point‖ :=
      linearBound
    _ = ‖Complex.ofRealCLM‖ *
        (|coefficient index| *
          ‖iteratedFDeriv ℝ order
            (plateauCutoff ∘ exteriorCutoffScale index) point‖) := by
      rw [iteratedFDeriv_const_smul_apply'
        (cutoffSmooth.of_le
          (WithTop.coe_le_coe.mpr
            (show (order : ℕ∞) ≤ ⊤ from le_top))), norm_smul,
        Real.norm_eq_abs]
    _ ≤ ‖Complex.ofRealCLM‖ *
        (|coefficient index| *
          (cutoffCompositeJetBound order point * node index ^ order)) := by
      gcongr
      exact cutoffComposite_iteratedFDeriv_norm_le_point
        order index point nonzero
    _ = exteriorScalarJetBound order point *
        (|coefficient index| * node index ^ order) := by
      unfold exteriorScalarJetBound
      ring

noncomputable def exteriorSummandPointBound {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index order : ℕ)
    (point : SpatialCell) : ℝ :=
  ∑ derivativeOrder ∈ Finset.range (order + 1),
    (order.choose derivativeOrder : ℝ) *
      exteriorScalarJetBound derivativeOrder point *
      reflectedCompositePointBound field index
        (order - derivativeOrder) point

theorem exteriorSummandPointBound_nonnegative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index order : ℕ)
    (point : SpatialCell) :
    0 ≤ exteriorSummandPointBound field index order point := by
  unfold exteriorSummandPointBound
  apply Finset.sum_nonneg
  intro derivativeOrder _
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _)
      (exteriorScalarJetBound_nonnegative derivativeOrder point))
    (reflectedCompositePointBound_nonnegative field index _ point)

theorem exteriorSummand_iteratedFDeriv_norm_le_point
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (index order : ℕ) (point : SpatialCell)
    (outside : 1 < ‖planarPart point‖) :
    ‖iteratedFDeriv ℝ order
        (exteriorSummandCellLift field index) point‖ ≤
      exteriorSummandPointBound field index order point *
        (|coefficient index| * node index ^ order) := by
  have nonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at outside
    norm_num at outside
  by_cases active : node index * (‖planarPart point‖ - 1) < 1
  · have activeMembership : point ∈ openExteriorActiveRegion index :=
      ⟨outside, active⟩
    have scalarSmooth : ContDiffOn ℝ ∞ (exteriorScalar index)
        (openExteriorActiveRegion index) := by
      intro other otherMembership
      exact (exteriorScalar_contDiffAt index other
        (closedExteriorActiveRegion_planarPart_ne_zero index
          ⟨otherMembership.1.le, otherMembership.2.le⟩)).contDiffWithinAt
    have compositeSmooth : ContDiffOn ℝ ∞
        (diskCellLift field.value ∘ reflectedSpatialCell index)
        (openExteriorActiveRegion index) :=
      ((diskCellLift_comp_reflectedSpatialCell_hasFTaylorSeriesUpToOn_active
        field index).contDiffOn).mono
          (openExteriorActiveRegion_subset_closedExteriorActiveRegion index)
    have productBound := norm_iteratedFDerivWithin_smul_le
      (𝕜 := ℝ) (N := ∞) (n := order)
      scalarSmooth compositeSmooth
      (openExteriorActiveRegion_isOpen index).uniqueDiffOn activeMembership
      (show (order : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr
          (show (order : ℕ∞) ≤ ⊤ from le_top))
    have withinProductEquality := iteratedFDerivWithin_of_isOpen
      (𝕜 := ℝ)
      (f := fun candidate => exteriorScalar index candidate •
        (diskCellLift field.value ∘ reflectedSpatialCell index) candidate)
      order (openExteriorActiveRegion_isOpen index) activeMembership
    rw [withinProductEquality] at productBound
    have scalarWithinEquality (derivativeOrder : ℕ) :=
      iteratedFDerivWithin_of_isOpen
        (𝕜 := ℝ) (f := exteriorScalar index) derivativeOrder
        (openExteriorActiveRegion_isOpen index) activeMembership
    have compositeWithinEquality (derivativeOrder : ℕ) :=
      iteratedFDerivWithin_of_isOpen
        (𝕜 := ℝ)
        (f := diskCellLift field.value ∘ reflectedSpatialCell index)
        derivativeOrder (openExteriorActiveRegion_isOpen index) activeMembership
    simp_rw [scalarWithinEquality, compositeWithinEquality] at productBound
    rw [show exteriorSummandCellLift field index = fun candidate =>
        exteriorScalar index candidate •
          (diskCellLift field.value ∘ reflectedSpatialCell index) candidate by
      funext other
      exact exteriorSummandCellLift_formula field index other]
    calc
      ‖iteratedFDeriv ℝ order (fun candidate => exteriorScalar index candidate •
          (diskCellLift field.value ∘ reflectedSpatialCell index) candidate) point‖ ≤
        ∑ derivativeOrder ∈ Finset.range (order + 1),
          (order.choose derivativeOrder : ℝ) *
            ‖iteratedFDeriv ℝ derivativeOrder (exteriorScalar index) point‖ *
            ‖iteratedFDeriv ℝ (order - derivativeOrder)
              (diskCellLift field.value ∘ reflectedSpatialCell index) point‖ :=
        productBound
      _ ≤ ∑ derivativeOrder ∈ Finset.range (order + 1),
          ((order.choose derivativeOrder : ℝ) *
            exteriorScalarJetBound derivativeOrder point *
            reflectedCompositePointBound field index
              (order - derivativeOrder) point) *
          (|coefficient index| * node index ^ order) := by
        apply Finset.sum_le_sum
        intro derivativeOrder membership
        have upper : derivativeOrder ≤ order :=
          Nat.le_of_lt_succ (Finset.mem_range.mp membership)
        have scalarBound := exteriorScalar_iteratedFDeriv_norm_le_point
          derivativeOrder index point nonzero
        have compositeBound := reflectedCompositeTaylorSeries_norm_le_point
          field index (order - derivativeOrder) point nonzero
        rw [reflectedCompositeTaylorSeries_eq_iteratedFDeriv_of_mem_openActive
          field index (order - derivativeOrder) point activeMembership]
          at compositeBound
        calc
          (order.choose derivativeOrder : ℝ) *
              ‖iteratedFDeriv ℝ derivativeOrder (exteriorScalar index) point‖ *
              ‖iteratedFDeriv ℝ (order - derivativeOrder)
                (diskCellLift field.value ∘ reflectedSpatialCell index) point‖ ≤
            (order.choose derivativeOrder : ℝ) *
              (exteriorScalarJetBound derivativeOrder point *
                (|coefficient index| * node index ^ derivativeOrder)) *
              (reflectedCompositePointBound field index
                  (order - derivativeOrder) point *
                node index ^ (order - derivativeOrder)) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left scalarBound (Nat.cast_nonneg _)
            · exact compositeBound
            · exact norm_nonneg _
            · exact mul_nonneg (Nat.cast_nonneg _)
                (mul_nonneg
                  (exteriorScalarJetBound_nonnegative derivativeOrder point)
                  (mul_nonneg (abs_nonneg _)
                    (pow_nonneg (node_positive index).le _)))
          _ = ((order.choose derivativeOrder : ℝ) *
                exteriorScalarJetBound derivativeOrder point *
                reflectedCompositePointBound field index
                  (order - derivativeOrder) point) *
              (|coefficient index| * node index ^ order) := by
            have powerEquality : node index ^ derivativeOrder *
                node index ^ (order - derivativeOrder) = node index ^ order := by
              rw [← pow_add, Nat.add_sub_of_le upper]
            rw [← powerEquality]
            ring
      _ = exteriorSummandPointBound field index order point *
          (|coefficient index| * node index ^ order) := by
        rw [exteriorSummandPointBound, Finset.sum_mul]
  · have scaleAbove : cutoffSupportWidth <
        node index * (‖planarPart point‖ - 1) := by
      have oneLe : 1 ≤ node index * (‖planarPart point‖ - 1) :=
        le_of_not_gt active
      norm_num [cutoffSupportWidth, collarWidth] at oneLe ⊢
      linarith
    have scaleContinuous : ContinuousAt (fun other : SpatialCell =>
        node index * (‖planarPart other‖ - 1)) point :=
      ((continuous_norm.comp continuous_planarPart).continuousAt.sub
        continuousAt_const).const_mul _
    have eventuallyInactive : ∀ᶠ other in 𝓝 point,
        cutoffSupportWidth ≤ node index * (‖planarPart other‖ - 1) :=
      (scaleContinuous.eventually (Ioi_mem_nhds scaleAbove)).mono
        fun _ inequality => inequality.le
    have summandZero : exteriorSummandCellLift field index =ᶠ[𝓝 point]
        fun _ => (0 : ComplexEuclidean dimension) := by
      filter_upwards [eventuallyInactive] with other inactive
      simp [exteriorSummandCellLift_formula, plateauCutoff_zero _ inactive]
    have derivativeZero :=
      (summandZero.iteratedFDeriv ℝ order).eq_of_nhds
    rw [derivativeZero]
    have constantDerivativeZero :
        iteratedFDeriv ℝ order
          (fun _ : SpatialCell => (0 : ComplexEuclidean dimension)) point = 0 := by
      rcases eq_or_ne order 0 with rfl | positive
      · rfl
      · rw [iteratedFDeriv_const_of_ne positive
          (0 : ComplexEuclidean dimension)]
        simp
    rw [constantDerivativeZero, norm_zero]
    exact mul_nonneg (exteriorSummandPointBound_nonnegative field index order point)
      (mul_nonneg (abs_nonneg _) (pow_nonneg (node_positive index).le _))

noncomputable def closedDerivativeGradePointSum {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade index : ℕ)
    (point : SpatialCell) : ℝ :=
  ∑ order ∈ Finset.range (grade + 1),
    closedHigherDerivativePointBound field order
      (reflectedSpatialCell index point)

theorem closedDerivativeGradePointSum_nonnegative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade index : ℕ)
    (point : SpatialCell) :
    0 ≤ closedDerivativeGradePointSum field grade index point := by
  unfold closedDerivativeGradePointSum
  exact Finset.sum_nonneg fun order _ =>
    closedHigherDerivativePointBound_nonnegative field order _

noncomputable def reflectionPartitionGeometry
    (order : ℕ) (point : SpatialCell) : ℝ :=
  ∑ partition : OrderedFinpartition order,
    ∏ position : Fin partition.length,
      reflectionJetBound (partition.partSize position) point

theorem reflectionPartitionGeometry_nonnegative
    (order : ℕ) (point : SpatialCell) :
    0 ≤ reflectionPartitionGeometry order point := by
  unfold reflectionPartitionGeometry
  exact Finset.sum_nonneg fun partition _ =>
    Finset.prod_nonneg fun position _ =>
      reflectionJetBound_nonnegative (partition.partSize position) point

theorem reflectedCompositePointBound_le_gradeSource
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade index order : ℕ) (point : SpatialCell) (upper : order ≤ grade) :
    reflectedCompositePointBound field index order point ≤
      closedDerivativeGradePointSum field grade index point *
        reflectionPartitionGeometry order point := by
  rw [reflectedCompositePointBound, reflectionPartitionGeometry]
  calc
    (∑ partition : OrderedFinpartition order,
        closedHigherDerivativePointBound field partition.length
            (reflectedSpatialCell index point) *
          ∏ position : Fin partition.length,
            reflectionJetBound (partition.partSize position) point) ≤
      ∑ partition : OrderedFinpartition order,
        closedDerivativeGradePointSum field grade index point *
          ∏ position : Fin partition.length,
            reflectionJetBound (partition.partSize position) point := by
      apply Finset.sum_le_sum
      intro partition _
      apply mul_le_mul_of_nonneg_right
      · unfold closedDerivativeGradePointSum
        exact Finset.single_le_sum
          (fun candidate _ =>
            closedHigherDerivativePointBound_nonnegative field candidate _)
          (Finset.mem_range.mpr (lt_of_le_of_lt
            (OrderedFinpartition.length_le partition)
            (Nat.lt_succ_of_le upper)))
      · exact Finset.prod_nonneg fun position _ =>
          reflectionJetBound_nonnegative (partition.partSize position) point
    _ = closedDerivativeGradePointSum field grade index point *
        ∑ partition : OrderedFinpartition order,
          ∏ position : Fin partition.length,
            reflectionJetBound (partition.partSize position) point := by
      rw [Finset.mul_sum]

noncomputable def exteriorOrderGeometry
    (order : ℕ) (point : SpatialCell) : ℝ :=
  ∑ derivativeOrder ∈ Finset.range (order + 1),
    (order.choose derivativeOrder : ℝ) *
      exteriorScalarJetBound derivativeOrder point *
      reflectionPartitionGeometry (order - derivativeOrder) point

theorem exteriorOrderGeometry_nonnegative
    (order : ℕ) (point : SpatialCell) :
    0 ≤ exteriorOrderGeometry order point := by
  unfold exteriorOrderGeometry
  apply Finset.sum_nonneg
  intro derivativeOrder _
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _)
      (exteriorScalarJetBound_nonnegative derivativeOrder point))
    (reflectionPartitionGeometry_nonnegative _ point)

theorem exteriorSummandPointBound_le_orderGeometry
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade index order : ℕ) (point : SpatialCell) (upper : order ≤ grade) :
    exteriorSummandPointBound field index order point ≤
      exteriorOrderGeometry order point *
        closedDerivativeGradePointSum field grade index point := by
  rw [exteriorSummandPointBound, exteriorOrderGeometry]
  calc
    (∑ derivativeOrder ∈ Finset.range (order + 1),
        (order.choose derivativeOrder : ℝ) *
          exteriorScalarJetBound derivativeOrder point *
          reflectedCompositePointBound field index
            (order - derivativeOrder) point) ≤
      ∑ derivativeOrder ∈ Finset.range (order + 1),
        ((order.choose derivativeOrder : ℝ) *
          exteriorScalarJetBound derivativeOrder point *
          reflectionPartitionGeometry (order - derivativeOrder) point) *
            closedDerivativeGradePointSum field grade index point := by
      apply Finset.sum_le_sum
      intro derivativeOrder membership
      have derivativeUpper : derivativeOrder ≤ order :=
        Nat.le_of_lt_succ (Finset.mem_range.mp membership)
      calc
        (order.choose derivativeOrder : ℝ) *
            exteriorScalarJetBound derivativeOrder point *
            reflectedCompositePointBound field index
              (order - derivativeOrder) point ≤
          (order.choose derivativeOrder : ℝ) *
            exteriorScalarJetBound derivativeOrder point *
            (closedDerivativeGradePointSum field grade index point *
              reflectionPartitionGeometry (order - derivativeOrder) point) :=
          mul_le_mul_of_nonneg_left
            (reflectedCompositePointBound_le_gradeSource field grade index
              (order - derivativeOrder) point
              ((Nat.sub_le order derivativeOrder).trans upper))
            (mul_nonneg (Nat.cast_nonneg _)
              (exteriorScalarJetBound_nonnegative derivativeOrder point))
        _ = ((order.choose derivativeOrder : ℝ) *
              exteriorScalarJetBound derivativeOrder point *
              reflectionPartitionGeometry (order - derivativeOrder) point) *
            closedDerivativeGradePointSum field grade index point := by ring
    _ = (∑ derivativeOrder ∈ Finset.range (order + 1),
          (order.choose derivativeOrder : ℝ) *
            exteriorScalarJetBound derivativeOrder point *
            reflectionPartitionGeometry (order - derivativeOrder) point) *
        closedDerivativeGradePointSum field grade index point := by
      rw [Finset.sum_mul]

noncomputable def exteriorGradeGeometry
    (grade : ℕ) (point : SpatialCell) : ℝ :=
  ∑ order ∈ Finset.range (grade + 1), exteriorOrderGeometry order point

theorem exteriorGradeGeometry_nonnegative
    (grade : ℕ) (point : SpatialCell) :
    0 ≤ exteriorGradeGeometry grade point := by
  unfold exteriorGradeGeometry
  exact Finset.sum_nonneg fun order _ =>
    exteriorOrderGeometry_nonnegative order point

theorem exteriorSummandPointBound_le_gradeGeometry
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade index order : ℕ) (point : SpatialCell) (upper : order ≤ grade) :
    exteriorSummandPointBound field index order point ≤
      exteriorGradeGeometry grade point *
        closedDerivativeGradePointSum field grade index point := by
  calc
    exteriorSummandPointBound field index order point ≤
        exteriorOrderGeometry order point *
          closedDerivativeGradePointSum field grade index point :=
      exteriorSummandPointBound_le_orderGeometry
        field grade index order point upper
    _ ≤ exteriorGradeGeometry grade point *
          closedDerivativeGradePointSum field grade index point := by
      apply mul_le_mul_of_nonneg_right
      · unfold exteriorGradeGeometry
        exact Finset.single_le_sum
          (fun candidate _ => exteriorOrderGeometry_nonnegative candidate point)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le upper))
      · exact closedDerivativeGradePointSum_nonnegative field grade index point

theorem exteriorSummand_iteratedFDeriv_norm_le_grade
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade index order : ℕ) (point : SpatialCell)
    (upper : order ≤ grade) (outside : 1 < ‖planarPart point‖) :
    ‖iteratedFDeriv ℝ order
        (exteriorSummandCellLift field index) point‖ ≤
      exteriorGradeGeometry grade point *
        (|coefficient index| * node index ^ grade) *
        closedDerivativeGradePointSum field grade index point := by
  have pointBound := exteriorSummand_iteratedFDeriv_norm_le_point
    field index order point outside
  have weightBound :
      |coefficient index| * node index ^ order ≤
        |coefficient index| * node index ^ grade :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (node_one_le index) upper) (abs_nonneg _)
  calc
    ‖iteratedFDeriv ℝ order
        (exteriorSummandCellLift field index) point‖ ≤
      exteriorSummandPointBound field index order point *
        (|coefficient index| * node index ^ order) := pointBound
    _ ≤ (exteriorGradeGeometry grade point *
          closedDerivativeGradePointSum field grade index point) *
        (|coefficient index| * node index ^ grade) := by
      exact mul_le_mul
        (exteriorSummandPointBound_le_gradeGeometry
          field grade index order point upper)
        weightBound
        (mul_nonneg (abs_nonneg _) (pow_nonneg (node_positive index).le _))
        (mul_nonneg (exteriorGradeGeometry_nonnegative grade point)
          (closedDerivativeGradePointSum_nonnegative field grade index point))
    _ = exteriorGradeGeometry grade point *
        (|coefficient index| * node index ^ grade) *
        closedDerivativeGradePointSum field grade index point := by ring

theorem reflectionJetBound_continuousOn (order : ℕ) :
    ContinuousOn (reflectionJetBound order) planarNonzeroRegion := by
  intro point nonzero
  unfold reflectionJetBound
  have normalizedContinuous : ContinuousAt (fun candidate =>
      iteratedFDeriv ℝ order normalizedSpatialCell candidate) point :=
    (normalizedSpatialCell_contDiffAt point nonzero).continuousAt_iteratedFDeriv
      (show (order : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr
          (show (order : ℕ∞) ≤ ⊤ from le_top))
  have identityContinuous : ContinuousAt (fun candidate : SpatialCell =>
      iteratedFDeriv ℝ order (id : SpatialCell → SpatialCell) candidate) point :=
    (contDiff_id.continuous_iteratedFDeriv'
      (𝕜 := ℝ) (m := order)).continuousAt
  exact (((normalizedContinuous.norm.add continuousAt_const).const_mul 2).add
    (identityContinuous.norm.add continuousAt_const)).continuousWithinAt

theorem radialJetEnvelope_continuousOn (order : ℕ) :
    ContinuousOn (radialJetEnvelope order) planarNonzeroRegion := by
  intro point nonzero
  unfold radialJetEnvelope
  apply ContinuousWithinAt.add continuousWithinAt_const
  exact tendsto_finsetSum Finset.univ (fun position _ => by
    have derivativeContinuous : ContinuousAt (fun candidate =>
        iteratedFDeriv ℝ (position.val + 1) radialOffset candidate) point :=
      (radialOffset_contDiffAt point nonzero).continuousAt_iteratedFDeriv
        (show (position.val + 1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by
          exact WithTop.coe_le_coe.mpr
            (show (position.val + 1 : ℕ∞) ≤ ⊤ from le_top))
    exact derivativeContinuous.continuousWithinAt.norm.add
      continuousWithinAt_const)

theorem cutoffCompositeJetBound_continuousOn (order : ℕ) :
    ContinuousOn (cutoffCompositeJetBound order) planarNonzeroRegion := by
  intro point nonzero
  unfold cutoffCompositeJetBound
  exact ((continuousWithinAt_const.mul continuousWithinAt_const).mul
    ((radialJetEnvelope_continuousOn order point nonzero).pow order))

theorem exteriorScalarJetBound_continuousOn (order : ℕ) :
    ContinuousOn (exteriorScalarJetBound order) planarNonzeroRegion := by
  intro point nonzero
  unfold exteriorScalarJetBound
  exact continuousWithinAt_const.mul
    (cutoffCompositeJetBound_continuousOn order point nonzero)

theorem reflectionPartitionGeometry_continuousOn (order : ℕ) :
    ContinuousOn (reflectionPartitionGeometry order) planarNonzeroRegion := by
  intro point nonzero
  unfold reflectionPartitionGeometry
  exact tendsto_finsetSum Finset.univ (fun partition _ =>
    tendsto_finsetProd Finset.univ (fun position _ =>
      reflectionJetBound_continuousOn
        (partition.partSize position) point nonzero))

theorem exteriorOrderGeometry_continuousOn (order : ℕ) :
    ContinuousOn (exteriorOrderGeometry order) planarNonzeroRegion := by
  intro point nonzero
  unfold exteriorOrderGeometry
  exact tendsto_finsetSum (Finset.range (order + 1))
    (fun derivativeOrder _ =>
      ((continuousWithinAt_const.mul
        (exteriorScalarJetBound_continuousOn derivativeOrder point nonzero)).mul
          (reflectionPartitionGeometry_continuousOn
            (order - derivativeOrder) point nonzero)))

theorem exteriorGradeGeometry_continuousOn (grade : ℕ) :
    ContinuousOn (exteriorGradeGeometry grade) planarNonzeroRegion := by
  intro point nonzero
  unfold exteriorGradeGeometry
  exact tendsto_finsetSum (Finset.range (grade + 1))
    (fun order _ => exteriorOrderGeometry_continuousOn order point nonzero)

def planarClosedGradeCollar : Set SpatialPlane :=
  {point | 1 ≤ ‖point‖ ∧ ‖point‖ ≤ outerSupportRadius}

theorem planarClosedGradeCollar_isCompact :
    IsCompact planarClosedGradeCollar := by
  apply (isCompact_closedBall (0 : SpatialPlane) outerSupportRadius).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro point membership
    change dist point 0 ≤ outerSupportRadius
    rw [dist_zero_right]
    exact membership.2

def closedGradeCollar : Set SpatialCell :=
  assembleSpatialCellCLM ''
    (planarClosedGradeCollar ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))

theorem closedGradeCollar_isCompact : IsCompact closedGradeCollar := by
  exact (planarClosedGradeCollar_isCompact.prod isCompact_Icc).image
    assembleSpatialCellCLM.continuous

theorem closedGradeCollar_subset_planarNonzeroRegion :
    closedGradeCollar ⊆ planarNonzeroRegion := by
  rintro point ⟨input, membership, rfl⟩
  change planarPart (assembleSpatialCell input.1 input.2) ≠ 0
  rw [planarPart_assembleSpatialCell]
  intro equality
  have lower := membership.1.1
  rw [equality, norm_zero] at lower
  norm_num at lower

theorem exists_exteriorGradeGeometry_bound (grade : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ point ∈ closedGradeCollar,
        exteriorGradeGeometry grade point ≤ bound := by
  have continuousOnCollar : ContinuousOn
      (exteriorGradeGeometry grade) closedGradeCollar :=
    (exteriorGradeGeometry_continuousOn grade).mono
      closedGradeCollar_subset_planarNonzeroRegion
  obtain ⟨bound, boundProperty⟩ := bddAbove_def.mp
    (closedGradeCollar_isCompact.bddAbove_image continuousOnCollar)
  refine ⟨max 0 bound, le_max_left _ _, ?_⟩
  intro point membership
  exact (boundProperty _ ⟨point, membership, rfl⟩).trans (le_max_right _ _)

noncomputable def closedDerivativeGradeGlobalBound {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ) : ℝ :=
  ∑ order ∈ Finset.range (grade + 1),
    closedHigherDerivativeBound field order

theorem closedDerivativeGradeGlobalBound_nonnegative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ) :
    0 ≤ closedDerivativeGradeGlobalBound field grade := by
  unfold closedDerivativeGradeGlobalBound
  exact Finset.sum_nonneg fun order _ =>
    closedHigherDerivativeBound_nonnegative field order

theorem closedHigherDerivativePointBound_le_global {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) :
    closedHigherDerivativePointBound field order point ≤
      closedHigherDerivativeBound field order := by
  rw [closedHigherDerivativePointBound, closedHigherDerivativeBound]
  apply Finset.sum_le_sum
  intro word _
  exact mul_le_mul_of_nonneg_left
    ((closedMixedDerivative field order word).norm_coe_le_norm _)
    (norm_nonneg _)

theorem closedDerivativeGradePointSum_le_global {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade index : ℕ)
    (point : SpatialCell) :
    closedDerivativeGradePointSum field grade index point ≤
      closedDerivativeGradeGlobalBound field grade := by
  rw [closedDerivativeGradePointSum, closedDerivativeGradeGlobalBound]
  apply Finset.sum_le_sum
  intro order _
  exact closedHigherDerivativePointBound_le_global field order _

theorem weighted_cauchy_finset
    {Index : Type*} (indices : Finset Index)
    (weight value : Index → ℝ)
    (weightNonnegative : ∀ index ∈ indices, 0 ≤ weight index) :
    (∑ index ∈ indices, weight index * value index) ^ 2 ≤
      (∑ index ∈ indices, weight index) *
        ∑ index ∈ indices, weight index * value index ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul indices
  · exact weightNonnegative
  · intro index membership
    exact mul_nonneg (weightNonnegative index membership) (sq_nonneg _)
  · intro index _
    ring_nf
    exact le_rfl

theorem weightedClosedDerivativeSquare_summable {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ)
    (point : SpatialCell) :
    Summable (fun index =>
      (|coefficient index| * node index ^ grade) *
        closedDerivativeGradePointSum field grade index point ^ 2) := by
  let globalBound := closedDerivativeGradeGlobalBound field grade
  have globalNonnegative : 0 ≤ globalBound :=
    closedDerivativeGradeGlobalBound_nonnegative field grade
  apply ((coefficient_absolute_moment_summable grade).mul_right
    (globalBound ^ 2)).of_norm_bounded
  intro index
  have pointNonnegative :=
    closedDerivativeGradePointSum_nonnegative field grade index point
  have pointBound := closedDerivativeGradePointSum_le_global
    field grade index point
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (mul_nonneg (abs_nonneg _)
      (pow_nonneg (node_positive index).le _)) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_left
    (sq_le_sq₀ pointNonnegative globalNonnegative |>.2 pointBound)
    (mul_nonneg (abs_nonneg _) (pow_nonneg (node_positive index).le _))

theorem plateauCutoff_iteratedFDeriv_zero_support (order : ℕ) :
    iteratedFDeriv ℝ order plateauCutoff cutoffSupportWidth = 0 := by
  rcases eq_or_ne order 0 with rfl | orderNonzero
  · apply ContinuousMultilinearMap.ext
    intro directions
    rw [iteratedFDeriv_zero_apply,
      plateauCutoff_zero cutoffSupportWidth le_rfl]
    rfl
  · have orderPositive : 0 < order := Nat.pos_of_ne_zero orderNonzero
    have derivativeContinuous : Continuous (iteratedDeriv order plateauCutoff) :=
      (plateauCutoff_smooth.of_le
        (WithTop.coe_le_coe.mpr
          (show (order : ℕ∞) ≤ ⊤ from le_top))).continuous_iteratedDeriv
        order (by exact_mod_cast le_rfl)
    have equalityOn : Set.EqOn (iteratedDeriv order plateauCutoff)
        (fun _ : ℝ => 0) (Set.Ioi cutoffSupportWidth) := by
      intro scale membership
      exact plateauCutoff_iteratedDeriv_zero_right
        order orderPositive scale membership
    have boundaryMembership : cutoffSupportWidth ∈
        closure (Set.Ioi cutoffSupportWidth) := by
      rw [closure_Ioi]
      exact Set.mem_Ici.mpr le_rfl
    have derivativeZero :=
      (equalityOn.closure derivativeContinuous continuous_const)
        boundaryMembership
    apply norm_eq_zero.mp
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, derivativeZero, norm_zero]

theorem cutoffComposite_iteratedFDeriv_eq_zero_of_supportBoundary
    (order index : ℕ) (point : SpatialCell)
    (nonzero : planarPart point ≠ 0)
    (supportBoundary : exteriorCutoffScale index point = cutoffSupportWidth) :
    iteratedFDeriv ℝ order
      (plateauCutoff ∘ exteriorCutoffScale index) point = 0 := by
  have outerBounds : ∀ derivativeOrder, derivativeOrder ≤ order →
      ‖iteratedFDerivWithin ℝ derivativeOrder plateauCutoff Set.univ
        (exteriorCutoffScale index point)‖ ≤ (0 : ℝ) := by
    intro derivativeOrder _
    rw [iteratedFDerivWithin_univ, supportBoundary,
      plateauCutoff_iteratedFDeriv_zero_support, norm_zero]
  have innerBounds : ∀ derivativeOrder, 1 ≤ derivativeOrder →
      derivativeOrder ≤ order →
      ‖iteratedFDerivWithin ℝ derivativeOrder (exteriorCutoffScale index)
        planarNonzeroRegion point‖ ≤
        (radialJetEnvelope order point * node index) ^ derivativeOrder := by
    intro derivativeOrder positive upper
    rw [iteratedFDerivWithin_of_isOpen derivativeOrder
      planarNonzeroRegion_isOpen nonzero]
    change ‖iteratedFDeriv ℝ derivativeOrder
      (fun point => node index • radialOffset point) point‖ ≤ _
    have radialSmooth : ContDiffAt ℝ derivativeOrder radialOffset point :=
      (radialOffset_contDiffAt point nonzero).of_le
        (WithTop.coe_le_coe.mpr
          (show (derivativeOrder : ℕ∞) ≤ ⊤ from le_top))
    rw [iteratedFDeriv_const_smul_apply' radialSmooth, norm_smul,
      Real.norm_eq_abs, abs_of_pos (node_positive index)]
    have derivativeBound :
        ‖iteratedFDeriv ℝ derivativeOrder radialOffset point‖ ≤
          radialJetEnvelope order point := by
      linarith [radialJet_le_envelope point positive upper]
    have baseOne : 1 ≤ radialJetEnvelope order point * node index := by
      simpa only [one_mul] using
        mul_le_mul (radialJetEnvelope_one_le order point)
          (node_one_le index) zero_le_one
          (zero_le_one.trans (radialJetEnvelope_one_le order point))
    calc
      node index * ‖iteratedFDeriv ℝ derivativeOrder radialOffset point‖ ≤
          node index * radialJetEnvelope order point :=
        mul_le_mul_of_nonneg_left derivativeBound (node_positive index).le
      _ = radialJetEnvelope order point * node index := mul_comm _ _
      _ ≤ (radialJetEnvelope order point * node index) ^ derivativeOrder := by
        simpa only [pow_one] using pow_le_pow_right₀ baseOne positive
  have compositionBound := norm_iteratedFDerivWithin_comp_le
    (𝕜 := ℝ) (n := order) (N := ∞)
    (s := planarNonzeroRegion) (t := Set.univ)
    plateauCutoff_smooth.contDiffOn
    (exteriorCutoffScale_contDiffOn_planarNonzeroRegion index)
    (show (order : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by
      exact WithTop.coe_le_coe.mpr
        (show (order : ℕ∞) ≤ ⊤ from le_top))
    uniqueDiffOn_univ planarNonzeroRegion_isOpen.uniqueDiffOn
    (mapsTo_univ _ _) nonzero (C := 0)
    (D := radialJetEnvelope order point * node index)
    outerBounds innerBounds
  have withinEquality := iteratedFDerivWithin_of_isOpen
    (𝕜 := ℝ) (f := plateauCutoff ∘ exteriorCutoffScale index)
    order planarNonzeroRegion_isOpen nonzero
  apply norm_eq_zero.mp
  rw [← withinEquality]
  exact le_antisymm (compositionBound.trans (by simp)) (norm_nonneg _)

theorem exteriorScalar_iteratedFDeriv_eq_zero_of_supportBoundary
    (order index : ℕ) (point : SpatialCell)
    (nonzero : planarPart point ≠ 0)
    (supportBoundary : exteriorCutoffScale index point = cutoffSupportWidth) :
    iteratedFDeriv ℝ order (exteriorScalar index) point = 0 := by
  have scaleSmooth : ContDiffAt ℝ ∞ (exteriorCutoffScale index) point :=
    ((radialOffset_contDiffAt point nonzero).const_smul (node index))
  have cutoffSmooth : ContDiffAt ℝ ∞
      (plateauCutoff ∘ exteriorCutoffScale index) point :=
    plateauCutoff_smooth.contDiffAt.comp point scaleSmooth
  have functionEquality : exteriorScalar index =
      Complex.ofRealCLM ∘ (fun candidate => coefficient index •
        (plateauCutoff ∘ exteriorCutoffScale index) candidate) := by
    funext other
    simp [exteriorScalar, exteriorCutoffScale, radialOffset,
      Function.comp_apply]
  rw [functionEquality]
  rw [Complex.ofRealCLM.iteratedFDeriv_comp_left
    (cutoffSmooth.const_smul (coefficient index))
    (show (order : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by
      exact WithTop.coe_le_coe.mpr
        (show (order : ℕ∞) ≤ ⊤ from le_top))]
  rw [iteratedFDeriv_const_smul_apply'
    (cutoffSmooth.of_le
      (WithTop.coe_le_coe.mpr
        (show (order : ℕ∞) ≤ ⊤ from le_top)))]
  rw [cutoffComposite_iteratedFDeriv_eq_zero_of_supportBoundary
    order index point nonzero supportBoundary]
  apply ContinuousMultilinearMap.ext
  intro directions
  simp

theorem exteriorSummand_iteratedFDeriv_eq_zero_of_supportBoundary
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (order index : ℕ) (point : SpatialCell)
    (outside : 1 < ‖planarPart point‖)
    (supportBoundary :
      node index * (‖planarPart point‖ - 1) = cutoffSupportWidth) :
    iteratedFDeriv ℝ order
      (exteriorSummandCellLift field index) point = 0 := by
  have nonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at outside
    norm_num at outside
  have active : node index * (‖planarPart point‖ - 1) < 1 := by
    rw [supportBoundary, collar_constants.2.2.1]
    norm_num
  have activeMembership : point ∈ openExteriorActiveRegion index :=
    ⟨outside, active⟩
  have scalarSmooth : ContDiffOn ℝ ∞ (exteriorScalar index)
      (openExteriorActiveRegion index) := by
    intro other otherMembership
    exact (exteriorScalar_contDiffAt index other
      (closedExteriorActiveRegion_planarPart_ne_zero index
        ⟨otherMembership.1.le, otherMembership.2.le⟩)).contDiffWithinAt
  have compositeSmooth : ContDiffOn ℝ ∞
      (diskCellLift field.value ∘ reflectedSpatialCell index)
      (openExteriorActiveRegion index) :=
    ((diskCellLift_comp_reflectedSpatialCell_hasFTaylorSeriesUpToOn_active
      field index).contDiffOn).mono
        (openExteriorActiveRegion_subset_closedExteriorActiveRegion index)
  have productBound := norm_iteratedFDerivWithin_smul_le
    (𝕜 := ℝ) (N := ∞) (n := order)
    scalarSmooth compositeSmooth
    (openExteriorActiveRegion_isOpen index).uniqueDiffOn activeMembership
    (show (order : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by
      exact WithTop.coe_le_coe.mpr
        (show (order : ℕ∞) ≤ ⊤ from le_top))
  have withinProductEquality := iteratedFDerivWithin_of_isOpen
    (𝕜 := ℝ)
    (f := fun candidate => exteriorScalar index candidate •
      (diskCellLift field.value ∘ reflectedSpatialCell index) candidate)
    order (openExteriorActiveRegion_isOpen index) activeMembership
  rw [withinProductEquality] at productBound
  have scalarWithinEquality (derivativeOrder : ℕ) :=
    iteratedFDerivWithin_of_isOpen
      (𝕜 := ℝ) (f := exteriorScalar index) derivativeOrder
      (openExteriorActiveRegion_isOpen index) activeMembership
  have compositeWithinEquality (derivativeOrder : ℕ) :=
    iteratedFDerivWithin_of_isOpen
      (𝕜 := ℝ)
      (f := diskCellLift field.value ∘ reflectedSpatialCell index)
      derivativeOrder (openExteriorActiveRegion_isOpen index) activeMembership
  simp_rw [scalarWithinEquality, compositeWithinEquality] at productBound
  rw [show exteriorSummandCellLift field index = fun candidate =>
      exteriorScalar index candidate •
        (diskCellLift field.value ∘ reflectedSpatialCell index) candidate by
    funext other
    exact exteriorSummandCellLift_formula field index other]
  apply norm_eq_zero.mp
  apply le_antisymm
  · refine productBound.trans ?_
    apply Finset.sum_nonpos
    intro derivativeOrder membership
    have scalarZero :=
      exteriorScalar_iteratedFDeriv_eq_zero_of_supportBoundary
        derivativeOrder index point nonzero (by
          simpa [exteriorCutoffScale, radialOffset] using supportBoundary)
    rw [scalarZero, norm_zero]
    simp
  · exact norm_nonneg _

theorem exteriorSummand_iteratedFDeriv_eq_zero_of_not_mem_supportAnnulus
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (order index : ℕ) (point : SpatialCell)
    (outside : 1 < ‖planarPart point‖)
    (notSupported : planarPart point ∉ exteriorSupportAnnulus index) :
    iteratedFDeriv ℝ order
      (exteriorSummandCellLift field index) point = 0 := by
  have scaleLower : cutoffSupportWidth ≤
      node index * (‖planarPart point‖ - 1) := by
    by_contra scaleNotLower
    apply notSupported
    exact ⟨outside, lt_of_not_ge scaleNotLower⟩
  rcases scaleLower.eq_or_lt with scaleBoundary | scaleAbove
  · exact exteriorSummand_iteratedFDeriv_eq_zero_of_supportBoundary
      field order index point outside scaleBoundary.symm
  · have scaleContinuous : ContinuousAt (fun other : SpatialCell =>
        node index * (‖planarPart other‖ - 1)) point :=
      ((continuous_norm.comp continuous_planarPart).continuousAt.sub
        continuousAt_const).const_mul _
    have eventuallyInactive : ∀ᶠ other in 𝓝 point,
        cutoffSupportWidth ≤ node index * (‖planarPart other‖ - 1) :=
      (scaleContinuous.eventually (Ioi_mem_nhds scaleAbove)).mono
        fun _ inequality => inequality.le
    have summandZero : exteriorSummandCellLift field index =ᶠ[𝓝 point]
        fun _ => (0 : ComplexEuclidean dimension) := by
      filter_upwards [eventuallyInactive] with other inactive
      simp [exteriorSummandCellLift_formula, plateauCutoff_zero _ inactive]
    have derivativeZero :=
      (summandZero.iteratedFDeriv ℝ order).eq_of_nhds
    rw [derivativeZero]
    rcases eq_or_ne order 0 with rfl | positive
    · rfl
    · rw [iteratedFDeriv_const_of_ne positive
        (0 : ComplexEuclidean dimension)]
      simp

theorem exteriorHigherDerivative_norm_sq_le_grade
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade order : ℕ) (point : SpatialCell)
    (upper : order ≤ grade) (outside : point ∈ strictExteriorRegion) :
    ‖exteriorHigherDerivative field order point‖ ^ 2 ≤
      exteriorGradeGeometry grade point ^ 2 * absoluteMoment grade *
        ∑' index,
          (|coefficient index| * node index ^ grade) *
            (exteriorSupportAnnulus index).indicator
              (fun _ => closedDerivativeGradePointSum
                field grade index point ^ 2) (planarPart point) := by
  obtain ⟨cutoff, neighborhood⟩ :=
    eventually_common_exterior_tail_zero field point outside
  have derivativeTailZero : ∀ index, cutoff ≤ index →
      iteratedFDeriv ℝ order
        (exteriorSummandCellLift field index) point = 0 := by
    intro index indexBound
    have summandZero : exteriorSummandCellLift field index =ᶠ[𝓝 point]
        fun _ => (0 : ComplexEuclidean dimension) := by
      filter_upwards [neighborhood] with candidate tail
      exact tail index indexBound
    have derivativeZero :=
      (summandZero.iteratedFDeriv ℝ order).eq_of_nhds
    rw [derivativeZero]
    rcases eq_or_ne order 0 with rfl | positive
    · rfl
    · rw [iteratedFDeriv_const_of_ne positive
        (0 : ComplexEuclidean dimension)]
      simp
  have finiteRepresentation : exteriorHigherDerivative field order point =
      ∑ index ∈ Finset.range cutoff,
        iteratedFDeriv ℝ order
          (exteriorSummandCellLift field index) point := by
    rw [exteriorHigherDerivative]
    exact (hasSum_sum_of_ne_finset_zero fun index outsideRange =>
      derivativeTailZero index (by simpa using outsideRange)).tsum_eq
  rw [finiteRepresentation]
  let weight : ℕ → ℝ := fun index =>
    |coefficient index| * node index ^ grade
  let source : ℕ → ℝ := fun index =>
    (exteriorSupportAnnulus index).indicator
      (fun _ => closedDerivativeGradePointSum field grade index point)
      (planarPart point)
  have normBound :
      ‖∑ index ∈ Finset.range cutoff,
          iteratedFDeriv ℝ order
            (exteriorSummandCellLift field index) point‖ ≤
        exteriorGradeGeometry grade point *
          ∑ index ∈ Finset.range cutoff, weight index * source index := by
    calc
      ‖∑ index ∈ Finset.range cutoff,
          iteratedFDeriv ℝ order
            (exteriorSummandCellLift field index) point‖ ≤
        ∑ index ∈ Finset.range cutoff,
          ‖iteratedFDeriv ℝ order
            (exteriorSummandCellLift field index) point‖ := norm_sum_le _ _
      _ ≤ ∑ index ∈ Finset.range cutoff,
          exteriorGradeGeometry grade point *
            (weight index * source index) := by
        apply Finset.sum_le_sum
        intro index _
        by_cases supported : planarPart point ∈ exteriorSupportAnnulus index
        · rw [show source index =
              closedDerivativeGradePointSum field grade index point by
            simp [source, Set.indicator, supported]]
          simpa only [weight, mul_assoc] using
            exteriorSummand_iteratedFDeriv_norm_le_grade
              field grade index order point upper outside
        · rw [exteriorSummand_iteratedFDeriv_eq_zero_of_not_mem_supportAnnulus
            field order index point outside supported, norm_zero]
          rw [show source index = 0 by
            simp [source, Set.indicator, supported]]
          simp
      _ = exteriorGradeGeometry grade point *
          ∑ index ∈ Finset.range cutoff, weight index * source index := by
        rw [Finset.mul_sum]
  have sumNonnegative : 0 ≤
      ∑ index ∈ Finset.range cutoff, weight index * source index := by
    apply Finset.sum_nonneg
    intro index _
    apply mul_nonneg
    · exact mul_nonneg (abs_nonneg _)
        (pow_nonneg (node_positive index).le _)
    · by_cases supported : planarPart point ∈ exteriorSupportAnnulus index
      · rw [show source index =
            closedDerivativeGradePointSum field grade index point by
          simp [source, Set.indicator, supported]]
        exact closedDerivativeGradePointSum_nonnegative field grade index point
      · rw [show source index = 0 by
          simp [source, Set.indicator, supported]]
  have squaredNormBound :
      ‖∑ index ∈ Finset.range cutoff,
          iteratedFDeriv ℝ order
            (exteriorSummandCellLift field index) point‖ ^ 2 ≤
        (exteriorGradeGeometry grade point *
          ∑ index ∈ Finset.range cutoff, weight index * source index) ^ 2 :=
    sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (exteriorGradeGeometry_nonnegative grade point)
        sumNonnegative) |>.2 normBound
  have cauchy := weighted_cauchy_finset (Finset.range cutoff)
    weight source (fun index _ =>
      mul_nonneg (abs_nonneg _) (pow_nonneg (node_positive index).le _))
  have finiteWeightBound :
      (∑ index ∈ Finset.range cutoff, weight index) ≤ absoluteMoment grade := by
    exact Summable.sum_le_tsum (Finset.range cutoff)
      (fun index _ =>
        mul_nonneg (abs_nonneg _) (pow_nonneg (node_positive index).le _))
      (coefficient_absolute_moment_summable grade)
  have sourceSquareSummable : Summable
      (fun index => weight index * source index ^ 2) := by
    apply (weightedClosedDerivativeSquare_summable field grade point).of_norm_bounded
    intro index
    by_cases supported : planarPart point ∈ exteriorSupportAnnulus index
    · rw [show source index =
          closedDerivativeGradePointSum field grade index point by
        simp [source, Set.indicator, supported]]
      simp only [weight]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (mul_nonneg (abs_nonneg _) (pow_nonneg (node_positive index).le _))
        (sq_nonneg _))]
    · rw [show source index = 0 by
        simp [source, Set.indicator, supported]]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, norm_zero]
      exact mul_nonneg
        (mul_nonneg (abs_nonneg _) (pow_nonneg (node_positive index).le _))
        (sq_nonneg _)
  have finiteSourceBound :
      (∑ index ∈ Finset.range cutoff, weight index * source index ^ 2) ≤
        ∑' index, weight index * source index ^ 2 := by
    exact Summable.sum_le_tsum (Finset.range cutoff)
      (fun index _ => mul_nonneg
        (mul_nonneg (abs_nonneg _) (pow_nonneg (node_positive index).le _))
        (sq_nonneg _))
      sourceSquareSummable
  calc
    ‖∑ index ∈ Finset.range cutoff,
        iteratedFDeriv ℝ order
          (exteriorSummandCellLift field index) point‖ ^ 2 ≤
      (exteriorGradeGeometry grade point *
        ∑ index ∈ Finset.range cutoff, weight index * source index) ^ 2 :=
      squaredNormBound
    _ = exteriorGradeGeometry grade point ^ 2 *
        (∑ index ∈ Finset.range cutoff, weight index * source index) ^ 2 := by
      ring
    _ ≤ exteriorGradeGeometry grade point ^ 2 *
        ((∑ index ∈ Finset.range cutoff, weight index) *
          ∑ index ∈ Finset.range cutoff, weight index * source index ^ 2) :=
      mul_le_mul_of_nonneg_left cauchy (sq_nonneg _)
    _ ≤ exteriorGradeGeometry grade point ^ 2 *
        (absoluteMoment grade *
          ∑' index, weight index * source index ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      exact mul_le_mul finiteWeightBound finiteSourceBound
        (Finset.sum_nonneg fun index _ => mul_nonneg
          (mul_nonneg (abs_nonneg _) (pow_nonneg (node_positive index).le _))
          (sq_nonneg _))
        (absoluteMoment_nonnegative grade)
      exact sq_nonneg _
    _ = exteriorGradeGeometry grade point ^ 2 * absoluteMoment grade *
        ∑' index,
          (|coefficient index| * node index ^ grade) *
            (exteriorSupportAnnulus index).indicator
              (fun _ => closedDerivativeGradePointSum
                field grade index point ^ 2) (planarPart point) := by
      rw [mul_assoc]
      congr 1
      congr 1
      apply tsum_congr
      intro index
      by_cases supported : planarPart point ∈ exteriorSupportAnnulus index
      · simp [weight, source, Set.indicator, supported]
      · simp [weight, source, Set.indicator, supported]

noncomputable def closedWordCoefficientSum (order : ℕ) : ℝ :=
  ∑ word : MixedCartesianWord order, ‖spatialCellWordCoefficient word‖

theorem closedWordCoefficientSum_nonnegative (order : ℕ) :
    0 ≤ closedWordCoefficientSum order := by
  unfold closedWordCoefficientSum
  positivity

noncomputable def closedDerivativeGradeQuadratic {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade index : ℕ)
    (point : SpatialCell) : ℝ :=
  ∑ order ∈ Finset.range (grade + 1),
    closedWordCoefficientSum order *
      ∑ word : MixedCartesianWord order,
        ‖spatialCellWordCoefficient word‖ *
          ‖closedMixedDerivative field order word
            (retractedDiskCell (reflectedSpatialCell index point))‖ ^ 2

theorem closedDerivativeGradeQuadratic_nonnegative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade index : ℕ)
    (point : SpatialCell) :
    0 ≤ closedDerivativeGradeQuadratic field grade index point := by
  unfold closedDerivativeGradeQuadratic
  apply Finset.sum_nonneg
  intro order _
  exact mul_nonneg (closedWordCoefficientSum_nonnegative order)
    (Finset.sum_nonneg fun word _ =>
      mul_nonneg (norm_nonneg _) (sq_nonneg _))

theorem closedHigherDerivativePointBound_sq_le_quadratic
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (index order : ℕ) (point : SpatialCell) :
    closedHigherDerivativePointBound field order
        (reflectedSpatialCell index point) ^ 2 ≤
      closedWordCoefficientSum order *
        ∑ word : MixedCartesianWord order,
          ‖spatialCellWordCoefficient word‖ *
            ‖closedMixedDerivative field order word
              (retractedDiskCell (reflectedSpatialCell index point))‖ ^ 2 := by
  have cauchy := weighted_cauchy_finset
    (Finset.univ : Finset (MixedCartesianWord order))
    (fun word => ‖spatialCellWordCoefficient word‖)
    (fun word => ‖closedMixedDerivative field order word
      (retractedDiskCell (reflectedSpatialCell index point))‖)
    (fun word _ => norm_nonneg _)
  simpa only [closedHigherDerivativePointBound,
    closedWordCoefficientSum] using cauchy

theorem closedDerivativeGradePointSum_sq_le_quadratic
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade index : ℕ) (point : SpatialCell) :
    closedDerivativeGradePointSum field grade index point ^ 2 ≤
      (grade + 1 : ℝ) *
        closedDerivativeGradeQuadratic field grade index point := by
  have outerCauchy := weighted_cauchy_finset (Finset.range (grade + 1))
    (fun _ : ℕ => (1 : ℝ))
    (fun order => closedHigherDerivativePointBound field order
      (reflectedSpatialCell index point))
    (fun _ _ => zero_le_one)
  have pointwiseQuadratic :
      (∑ order ∈ Finset.range (grade + 1),
        closedHigherDerivativePointBound field order
          (reflectedSpatialCell index point) ^ 2) ≤
      closedDerivativeGradeQuadratic field grade index point := by
    unfold closedDerivativeGradeQuadratic
    apply Finset.sum_le_sum
    intro order _
    exact closedHigherDerivativePointBound_sq_le_quadratic
      field index order point
  calc
    closedDerivativeGradePointSum field grade index point ^ 2 =
        (∑ order ∈ Finset.range (grade + 1),
          (1 : ℝ) * closedHigherDerivativePointBound field order
            (reflectedSpatialCell index point)) ^ 2 := by
      simp [closedDerivativeGradePointSum]
    _ ≤ (∑ order ∈ Finset.range (grade + 1), (1 : ℝ)) *
        ∑ order ∈ Finset.range (grade + 1),
          (1 : ℝ) * closedHigherDerivativePointBound field order
            (reflectedSpatialCell index point) ^ 2 := outerCauchy
    _ = (grade + 1 : ℝ) *
        ∑ order ∈ Finset.range (grade + 1),
          closedHigherDerivativePointBound field order
            (reflectedSpatialCell index point) ^ 2 := by simp
    _ ≤ (grade + 1 : ℝ) *
        closedDerivativeGradeQuadratic field grade index point :=
      mul_le_mul_of_nonneg_left pointwiseQuadratic (by positivity)

noncomputable def closedMixedSquaredDensity {dimension order : ℕ}
    (field : DiskCellClosedJet dimension) (word : MixedCartesianWord order)
    (cell : CellCircle) (point : SpatialPlane) : ℝ :=
  ‖closedDiskCellMultiDerivative field (mixedWordMultiIndex word)
    (radialRetraction point, cell)‖ ^ 2

theorem closedMixedSquaredDensity_continuous {dimension order : ℕ}
    (field : DiskCellClosedJet dimension) (word : MixedCartesianWord order)
    (cell : CellCircle) :
    Continuous (closedMixedSquaredDensity field word cell) := by
  unfold closedMixedSquaredDensity
  exact (((closedDiskCellMultiDerivative field
    (mixedWordMultiIndex word)).continuous.comp
      (continuous_radialRetraction.prodMk continuous_const)).norm).pow 2

theorem closedMixedSquaredDensity_reflected {dimension order : ℕ}
    (field : DiskCellClosedJet dimension) (word : MixedCartesianWord order)
    (index : ℕ) (cell : ℝ) (point : SpatialPlane) :
    closedMixedSquaredDensity field word (cell : CellCircle)
        (reflectedPoint index point) =
      ‖closedMixedDerivative field order word
        (retractedDiskCell
          (reflectedSpatialCell index (assembleSpatialCell point cell)))‖ ^ 2 := by
  rw [closedMixedDerivative_eq_multiIndexDerivative]
  simp only [closedMixedSquaredDensity, retractedDiskCell,
    reflectedSpatialCell_planarPart, planarPart_assembleSpatialCell]
  rfl

theorem closedMixedSquaredDensity_integral_eq {dimension order : ℕ}
    (field : DiskCellClosedJet dimension) (word : MixedCartesianWord order)
    (cell : CellCircle) :
    (∫ point in closedUnitDisk,
        closedMixedSquaredDensity field word cell point) =
      ∫ point : SpatialPlane,
        ‖closedDiskLift
          (fun diskPoint => closedDiskCellMultiDerivative field
            (mixedWordMultiIndex word) (diskPoint, cell)) point‖ ^ 2 := by
  rw [← integral_indicator (by
    rw [closedUnitDisk_eq_closedBall]
    exact Metric.isClosed_closedBall.measurableSet)]
  apply integral_congr_ae
  filter_upwards [] with point
  by_cases membership : point ∈ closedUnitDisk
  · rw [Set.indicator_of_mem membership, closedDiskLift, dif_pos membership]
    unfold closedMixedSquaredDensity
    have retractionEquality : radialRetraction point =
        (⟨point, membership⟩ : ClosedDisk) := by
      exact Subtype.ext (radialRetraction_val_of_mem point membership)
    rw [retractionEquality]
  · simp [Set.indicator, closedDiskLift, membership]

theorem closedMixedDerivative_reflected_integral_le {dimension order : ℕ}
    (field : DiskCellClosedJet dimension) (word : MixedCartesianWord order)
    (index : ℕ) (cell : ℝ) :
    (∫ point in exteriorSupportAnnulus index,
        ‖closedMixedDerivative field order word
          (retractedDiskCell
            (reflectedSpatialCell index (assembleSpatialCell point cell)))‖ ^ 2) ≤
      (7 / (5 * node index)) *
        ∫ point : SpatialPlane,
          ‖closedDiskLift
            (fun diskPoint => closedDiskCellMultiDerivative field
              (mixedWordMultiIndex word) (diskPoint, (cell : CellCircle))) point‖ ^ 2 := by
  rw [← closedMixedSquaredDensity_integral_eq field word (cell : CellCircle)]
  have collar := exteriorSupportAnnulus_reflected_integral_le index
    (closedMixedSquaredDensity field word (cell : CellCircle))
    (closedMixedSquaredDensity_continuous field word (cell : CellCircle))
    (fun point => sq_nonneg _)
  calc
    (∫ point in exteriorSupportAnnulus index,
        ‖closedMixedDerivative field order word
          (retractedDiskCell
            (reflectedSpatialCell index (assembleSpatialCell point cell)))‖ ^ 2) =
        ∫ point in exteriorSupportAnnulus index,
          closedMixedSquaredDensity field word (cell : CellCircle)
            (reflectedPoint index point) := by
      apply integral_congr_ae
      filter_upwards [] with point
      exact (closedMixedSquaredDensity_reflected
        field word index cell point).symm
    _ ≤ (7 / (5 * node index)) *
        ∫ point in closedUnitDisk,
          closedMixedSquaredDensity field word (cell : CellCircle) point := collar

noncomputable def closedDerivativeGradeSquaredDensity {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ)
    (cell : CellCircle) (point : SpatialPlane) : ℝ :=
  ∑ order ∈ Finset.range (grade + 1),
    closedWordCoefficientSum order *
      ∑ word : MixedCartesianWord order,
        ‖spatialCellWordCoefficient word‖ *
          closedMixedSquaredDensity field word cell point

theorem closedDerivativeGradeSquaredDensity_continuous {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ)
    (cell : CellCircle) :
    Continuous (closedDerivativeGradeSquaredDensity field grade cell) := by
  unfold closedDerivativeGradeSquaredDensity
  apply continuous_finsetSum
  intro order orderMembership
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro word wordMembership
  exact (closedMixedSquaredDensity_continuous field word cell).const_mul _

theorem closedDerivativeGradeSquaredDensity_nonnegative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ)
    (cell : CellCircle) (point : SpatialPlane) :
    0 ≤ closedDerivativeGradeSquaredDensity field grade cell point := by
  unfold closedDerivativeGradeSquaredDensity
  apply Finset.sum_nonneg
  intro order _
  apply mul_nonneg (closedWordCoefficientSum_nonnegative order)
  exact Finset.sum_nonneg fun word _ =>
    mul_nonneg (norm_nonneg _) (sq_nonneg _)

theorem closedDerivativeGradeSquaredDensity_reflected {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade index : ℕ)
    (cell : ℝ) (point : SpatialPlane) :
    closedDerivativeGradeSquaredDensity field grade (cell : CellCircle)
        (reflectedPoint index point) =
      closedDerivativeGradeQuadratic field grade index
        (assembleSpatialCell point cell) := by
  unfold closedDerivativeGradeSquaredDensity closedDerivativeGradeQuadratic
  apply Finset.sum_congr rfl
  intro order orderMembership
  congr 1
  apply Finset.sum_congr rfl
  intro word wordMembership
  rw [closedMixedSquaredDensity_reflected]

theorem closedDerivativeGradeQuadratic_reflected_integral_le
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade index : ℕ) (cell : ℝ) :
    (∫ point in exteriorSupportAnnulus index,
        closedDerivativeGradeQuadratic field grade index
          (assembleSpatialCell point cell)) ≤
      (7 / (5 * node index)) *
        ∫ point in closedUnitDisk,
          closedDerivativeGradeSquaredDensity field grade
            (cell : CellCircle) point := by
  have collar := exteriorSupportAnnulus_reflected_integral_le index
    (closedDerivativeGradeSquaredDensity field grade (cell : CellCircle))
    (closedDerivativeGradeSquaredDensity_continuous
      field grade (cell : CellCircle))
    (closedDerivativeGradeSquaredDensity_nonnegative
      field grade (cell : CellCircle))
  calc
    (∫ point in exteriorSupportAnnulus index,
        closedDerivativeGradeQuadratic field grade index
          (assembleSpatialCell point cell)) =
        ∫ point in exteriorSupportAnnulus index,
          closedDerivativeGradeSquaredDensity field grade (cell : CellCircle)
            (reflectedPoint index point) := by
      apply integral_congr_ae
      filter_upwards [] with point
      exact (closedDerivativeGradeSquaredDensity_reflected
        field grade index cell point).symm
    _ ≤ (7 / (5 * node index)) *
        ∫ point in closedUnitDisk,
          closedDerivativeGradeSquaredDensity field grade
            (cell : CellCircle) point := collar

noncomputable def closedDerivativeGradeCoefficient (grade : ℕ) : ℝ :=
  ∑ order ∈ Finset.range (grade + 1),
    closedWordCoefficientSum order *
      ∑ word : MixedCartesianWord order,
        ‖spatialCellWordCoefficient word‖

theorem closedDerivativeGradeCoefficient_nonnegative (grade : ℕ) :
    0 ≤ closedDerivativeGradeCoefficient grade := by
  unfold closedDerivativeGradeCoefficient
  apply Finset.sum_nonneg
  intro order _
  exact mul_nonneg (closedWordCoefficientSum_nonnegative order)
    (Finset.sum_nonneg fun word _ => norm_nonneg _)

theorem mixedWordMultiIndex_mem_diskCellMultiIndices {order grade : ℕ}
    (word : MixedCartesianWord order) (upper : order ≤ grade) :
    mixedWordMultiIndex word ∈ diskCellMultiIndices grade := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_range.mpr
        have countBound : (List.ofFn word).count 0 ≤
            (List.ofFn word).length := List.count_le_length
        simp only [List.length_ofFn] at countBound
        change (List.ofFn word).count 0 < grade + 1
        omega
      · apply Finset.mem_range.mpr
        have countBound : (List.ofFn word).count 1 ≤
            (List.ofFn word).length := List.count_le_length
        simp only [List.length_ofFn] at countBound
        change (List.ofFn word).count 1 < grade + 1
        omega
    · apply Finset.mem_range.mpr
      have countBound : (List.ofFn word).count 2 ≤
          (List.ofFn word).length := List.count_le_length
      simp only [List.length_ofFn] at countBound
      change (List.ofFn word).count 2 < grade + 1
      omega
  · simpa only [mixedWordMultiIndex_order] using upper

noncomputable def closedIndexSquaredDensity {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : DiskCellMultiIndex)
    (cell : CellCircle) (point : SpatialPlane) : ℝ :=
  ‖closedDiskCellMultiDerivative field index (radialRetraction point, cell)‖ ^ 2

theorem closedIndexSquaredDensity_continuous {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : DiskCellMultiIndex)
    (cell : CellCircle) :
    Continuous (closedIndexSquaredDensity field index cell) := by
  unfold closedIndexSquaredDensity
  exact (((closedDiskCellMultiDerivative field index).continuous.comp
    (continuous_radialRetraction.prodMk continuous_const)).norm).pow 2

noncomputable def closedDerivativeGradeUnweightedDensity {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ)
    (cell : CellCircle) (point : SpatialPlane) : ℝ :=
  ∑ index ∈ diskCellMultiIndices grade,
    closedIndexSquaredDensity field index cell point

theorem closedDerivativeGradeUnweightedDensity_continuous {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ)
    (cell : CellCircle) :
    Continuous (closedDerivativeGradeUnweightedDensity field grade cell) := by
  unfold closedDerivativeGradeUnweightedDensity
  apply continuous_finsetSum
  intro index indexMembership
  exact closedIndexSquaredDensity_continuous field index cell

theorem closedMixedSquaredDensity_le_gradeUnweighted {dimension order grade : ℕ}
    (field : DiskCellClosedJet dimension) (word : MixedCartesianWord order)
    (cell : CellCircle) (point : SpatialPlane) (upper : order ≤ grade) :
    closedMixedSquaredDensity field word cell point ≤
      closedDerivativeGradeUnweightedDensity field grade cell point := by
  unfold closedDerivativeGradeUnweightedDensity closedMixedSquaredDensity
    closedIndexSquaredDensity
  exact Finset.single_le_sum
    (fun index _ => sq_nonneg
      ‖closedDiskCellMultiDerivative field index (radialRetraction point, cell)‖)
    (mixedWordMultiIndex_mem_diskCellMultiIndices word upper)

theorem closedDerivativeGradeSquaredDensity_le_unweighted {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ)
    (cell : CellCircle) (point : SpatialPlane) :
    closedDerivativeGradeSquaredDensity field grade cell point ≤
      closedDerivativeGradeCoefficient grade *
        closedDerivativeGradeUnweightedDensity field grade cell point := by
  unfold closedDerivativeGradeSquaredDensity closedDerivativeGradeCoefficient
  calc
    (∑ order ∈ Finset.range (grade + 1),
        closedWordCoefficientSum order *
          ∑ word : MixedCartesianWord order,
            ‖spatialCellWordCoefficient word‖ *
              closedMixedSquaredDensity field word cell point) ≤
      ∑ order ∈ Finset.range (grade + 1),
        closedWordCoefficientSum order *
          ∑ word : MixedCartesianWord order,
            ‖spatialCellWordCoefficient word‖ *
              closedDerivativeGradeUnweightedDensity field grade cell point := by
      apply Finset.sum_le_sum
      intro order orderMembership
      apply mul_le_mul_of_nonneg_left _
        (closedWordCoefficientSum_nonnegative order)
      apply Finset.sum_le_sum
      intro word wordMembership
      apply mul_le_mul_of_nonneg_left
      · exact closedMixedSquaredDensity_le_gradeUnweighted
          field word cell point (by simpa using orderMembership)
      · exact norm_nonneg _
    _ = (∑ order ∈ Finset.range (grade + 1),
        closedWordCoefficientSum order *
          ∑ word : MixedCartesianWord order,
            ‖spatialCellWordCoefficient word‖) *
          closedDerivativeGradeUnweightedDensity field grade cell point := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro order orderMembership
      calc
        closedWordCoefficientSum order *
            (∑ word : MixedCartesianWord order,
              ‖spatialCellWordCoefficient word‖ *
                closedDerivativeGradeUnweightedDensity field grade cell point) =
          closedWordCoefficientSum order *
            ((∑ word : MixedCartesianWord order,
              ‖spatialCellWordCoefficient word‖) *
                closedDerivativeGradeUnweightedDensity field grade cell point) := by
            rw [Finset.sum_mul]
        _ = (closedWordCoefficientSum order *
            ∑ word : MixedCartesianWord order,
              ‖spatialCellWordCoefficient word‖) *
                closedDerivativeGradeUnweightedDensity field grade cell point := by
          ring

theorem closedIndexSquaredDensity_integral_eq {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : DiskCellMultiIndex)
    (cell : CellCircle) :
    (∫ point in closedUnitDisk,
        closedIndexSquaredDensity field index cell point) =
      ∫ point : SpatialPlane,
        ‖closedDiskLift
          (fun diskPoint => closedDiskCellMultiDerivative field index
            (diskPoint, cell)) point‖ ^ 2 := by
  rw [← integral_indicator (by
    rw [closedUnitDisk_eq_closedBall]
    exact Metric.isClosed_closedBall.measurableSet)]
  apply integral_congr_ae
  filter_upwards [] with point
  by_cases membership : point ∈ closedUnitDisk
  · rw [Set.indicator_of_mem membership, closedDiskLift, dif_pos membership]
    unfold closedIndexSquaredDensity
    have retractionEquality : radialRetraction point =
        (⟨point, membership⟩ : ClosedDisk) := by
      exact Subtype.ext (radialRetraction_val_of_mem point membership)
    rw [retractionEquality]
  · simp [Set.indicator, closedDiskLift, membership]

theorem closedDerivativeGradeUnweightedDensity_integral_eq {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ)
    (cell : CellCircle) :
    (∫ point in closedUnitDisk,
        closedDerivativeGradeUnweightedDensity field grade cell point) =
      ∑ index ∈ diskCellMultiIndices grade,
        ∫ point : SpatialPlane,
          ‖closedDiskLift
            (fun diskPoint => closedDiskCellMultiDerivative field index
              (diskPoint, cell)) point‖ ^ 2 := by
  unfold closedDerivativeGradeUnweightedDensity
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro index indexMembership
    exact closedIndexSquaredDensity_integral_eq field index cell
  · intro index indexMembership
    exact (closedIndexSquaredDensity_continuous field index cell).continuousOn
      |>.integrableOn_compact (by
        rw [closedUnitDisk_eq_closedBall]
        exact isCompact_closedBall (0 : SpatialPlane) 1)

noncomputable def closedGradeSpatialEnergy {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ)
    (cell : CellCircle) : ℝ :=
  ∑ index ∈ diskCellMultiIndices grade,
    ∫ point : SpatialPlane,
      ‖closedDiskLift
        (fun diskPoint => closedDiskCellMultiDerivative field index
          (diskPoint, cell)) point‖ ^ 2

theorem closedDerivativeGradeSquaredDensity_integral_le {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ)
    (cell : CellCircle) :
    (∫ point in closedUnitDisk,
        closedDerivativeGradeSquaredDensity field grade cell point) ≤
      closedDerivativeGradeCoefficient grade *
        closedGradeSpatialEnergy field grade cell := by
  have diskCompact : IsCompact closedUnitDisk := by
    rw [closedUnitDisk_eq_closedBall]
    exact isCompact_closedBall (0 : SpatialPlane) 1
  have sourceIntegrable : IntegrableOn
      (closedDerivativeGradeSquaredDensity field grade cell) closedUnitDisk :=
    (closedDerivativeGradeSquaredDensity_continuous field grade cell).continuousOn
      |>.integrableOn_compact diskCompact
  have targetIntegrable : IntegrableOn
      (fun point => closedDerivativeGradeCoefficient grade *
        closedDerivativeGradeUnweightedDensity field grade cell point)
      closedUnitDisk :=
    ((closedDerivativeGradeUnweightedDensity_continuous field grade cell).const_mul
      (closedDerivativeGradeCoefficient grade)).continuousOn
        |>.integrableOn_compact diskCompact
  calc
    (∫ point in closedUnitDisk,
        closedDerivativeGradeSquaredDensity field grade cell point) ≤
      ∫ point in closedUnitDisk,
        closedDerivativeGradeCoefficient grade *
          closedDerivativeGradeUnweightedDensity field grade cell point := by
      exact integral_mono sourceIntegrable targetIntegrable
        (fun point => closedDerivativeGradeSquaredDensity_le_unweighted
          field grade cell point)
    _ = closedDerivativeGradeCoefficient grade *
        ∫ point in closedUnitDisk,
          closedDerivativeGradeUnweightedDensity field grade cell point := by
      rw [integral_const_mul]
    _ = closedDerivativeGradeCoefficient grade *
        closedGradeSpatialEnergy field grade cell := by
      rw [closedDerivativeGradeUnweightedDensity_integral_eq]
      rfl

theorem exteriorSupportAnnulus_subset_planarClosedGradeCollar (index : ℕ) :
    exteriorSupportAnnulus index ⊆ planarClosedGradeCollar := by
  intro point membership
  change 1 < ‖point‖ ∧
    node index * (‖point‖ - 1) < cutoffSupportWidth at membership
  change 1 ≤ ‖point‖ ∧ ‖point‖ ≤ outerSupportRadius
  refine ⟨membership.1.le, ?_⟩
  have offsetNonnegative : 0 ≤ ‖point‖ - 1 := by linarith [membership.1]
  have nodeBound : 1 ≤ node index := node_one_le index
  have offsetComparison : ‖point‖ - 1 ≤
      node index * (‖point‖ - 1) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right nodeBound offsetNonnegative
  rw [collar_constants.2.2.1] at membership
  rw [collar_constants.2.2.2.2]
  linarith

theorem reflectedPoint_continuousOn_planarClosedGradeCollar (index : ℕ) :
    ContinuousOn (reflectedPoint index) planarClosedGradeCollar := by
  intro point membership
  have pointNonzero : point ≠ 0 := by
    intro equality
    have lower : 1 ≤ ‖point‖ := membership.1
    rw [equality, norm_zero] at lower
    norm_num at lower
  have normInverse : ContinuousAt (fun candidate : SpatialPlane => ‖candidate‖⁻¹)
      point := continuous_norm.continuousAt.inv₀
        (norm_ne_zero_iff.mpr pointNonzero)
  have radialDirection : ContinuousAt
      (fun candidate : SpatialPlane => ‖candidate‖⁻¹ • candidate) point :=
    normInverse.smul continuousAt_id
  have radialScalar : ContinuousAt
      (fun candidate : SpatialPlane =>
        1 - node index * (‖candidate‖ - 1)) point := by
    fun_prop
  exact (radialScalar.smul radialDirection).continuousWithinAt

theorem closedDerivativeGradeSquaredDensity_reflected_continuousOn
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade index : ℕ) (cell : CellCircle) :
    ContinuousOn
      (fun point => closedDerivativeGradeSquaredDensity field grade cell
        (reflectedPoint index point)) planarClosedGradeCollar := by
  exact (closedDerivativeGradeSquaredDensity_continuous field grade cell).comp_continuousOn
    (reflectedPoint_continuousOn_planarClosedGradeCollar index)

theorem closedDerivativeGradeSquaredDensity_reflected_integrableOn
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade index : ℕ) (cell : CellCircle) :
    IntegrableOn
      (fun point => closedDerivativeGradeSquaredDensity field grade cell
        (reflectedPoint index point)) (exteriorSupportAnnulus index) := by
  exact ((closedDerivativeGradeSquaredDensity_reflected_continuousOn
    field grade index cell).integrableOn_compact planarClosedGradeCollar_isCompact).mono_set
      (exteriorSupportAnnulus_subset_planarClosedGradeCollar index)

theorem closedGradeSpatialEnergy_nonnegative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ)
    (cell : CellCircle) :
    0 ≤ closedGradeSpatialEnergy field grade cell := by
  unfold closedGradeSpatialEnergy
  apply Finset.sum_nonneg
  intro index indexMembership
  exact integral_nonneg fun point => sq_nonneg _

theorem closedDerivativeGradeQuadratic_reflected_integral_le_energy
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade index : ℕ) (cell : ℝ) :
    (∫ point in exteriorSupportAnnulus index,
        closedDerivativeGradeQuadratic field grade index
          (assembleSpatialCell point cell)) ≤
      (7 / 5 : ℝ) * closedDerivativeGradeCoefficient grade *
        closedGradeSpatialEnergy field grade (cell : CellCircle) := by
  let sourceIntegral : ℝ := ∫ point in closedUnitDisk,
    closedDerivativeGradeSquaredDensity field grade (cell : CellCircle) point
  let gradeEnergy : ℝ :=
    closedGradeSpatialEnergy field grade (cell : CellCircle)
  have sourceNonnegative : 0 ≤ sourceIntegral := by
    apply integral_nonneg
    intro point
    exact closedDerivativeGradeSquaredDensity_nonnegative
      field grade (cell : CellCircle) point
  have energyNonnegative : 0 ≤ gradeEnergy :=
    closedGradeSpatialEnergy_nonnegative field grade (cell : CellCircle)
  have sourceBound : sourceIntegral ≤
      closedDerivativeGradeCoefficient grade * gradeEnergy :=
    closedDerivativeGradeSquaredDensity_integral_le
      field grade (cell : CellCircle)
  have factorNonnegative : 0 ≤ 7 / (5 * node index) :=
    div_nonneg (by norm_num)
      (mul_nonneg (by norm_num) (node_positive index).le)
  have factorBound : 7 / (5 * node index) ≤ (7 / 5 : ℝ) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) (node_positive index))).2
    nlinarith [node_one_le index]
  calc
    (∫ point in exteriorSupportAnnulus index,
        closedDerivativeGradeQuadratic field grade index
          (assembleSpatialCell point cell)) ≤
      (7 / (5 * node index)) * sourceIntegral :=
        closedDerivativeGradeQuadratic_reflected_integral_le
          field grade index cell
    _ ≤ (7 / (5 * node index)) *
        (closedDerivativeGradeCoefficient grade * gradeEnergy) :=
      mul_le_mul_of_nonneg_left sourceBound factorNonnegative
    _ ≤ (7 / 5 : ℝ) *
        (closedDerivativeGradeCoefficient grade * gradeEnergy) :=
      mul_le_mul_of_nonneg_right factorBound
        (mul_nonneg (closedDerivativeGradeCoefficient_nonnegative grade)
          energyNonnegative)
    _ = (7 / 5 : ℝ) * closedDerivativeGradeCoefficient grade *
        gradeEnergy := by ring

theorem closedDerivativeGradeQuadratic_reflected_integrableOn
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade index : ℕ) (cell : ℝ) :
    IntegrableOn
      (fun point => closedDerivativeGradeQuadratic field grade index
        (assembleSpatialCell point cell)) (exteriorSupportAnnulus index) := by
  have functionIdentity :
      (fun point => closedDerivativeGradeQuadratic field grade index
        (assembleSpatialCell point cell)) =
      (fun point => closedDerivativeGradeSquaredDensity field grade
        (cell : CellCircle) (reflectedPoint index point)) := by
    funext point
    exact (closedDerivativeGradeSquaredDensity_reflected
      field grade index cell point).symm
  rw [functionIdentity]
  exact closedDerivativeGradeSquaredDensity_reflected_integrableOn
    field grade index (cell : CellCircle)

noncomputable def exteriorGradeQuadraticTerm {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade index : ℕ)
    (cell : ℝ) (point : SpatialPlane) : ℝ :=
  (|coefficient index| * node index ^ grade) *
    (exteriorSupportAnnulus index).indicator
      (fun candidate => closedDerivativeGradeQuadratic field grade index
        (assembleSpatialCell candidate cell)) point

theorem exteriorGradeQuadraticTerm_nonnegative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade index : ℕ)
    (cell : ℝ) (point : SpatialPlane) :
    0 ≤ exteriorGradeQuadraticTerm field grade index cell point := by
  unfold exteriorGradeQuadraticTerm
  apply mul_nonneg
  · exact mul_nonneg (abs_nonneg _)
      (pow_nonneg (node_positive index).le _)
  · by_cases membership : point ∈ exteriorSupportAnnulus index
    · rw [Set.indicator_of_mem membership]
      exact closedDerivativeGradeQuadratic_nonnegative field grade index _
    · simp [Set.indicator, membership]

theorem exteriorGradeQuadraticTerm_integrable {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade index : ℕ)
    (cell : ℝ) :
    Integrable (exteriorGradeQuadraticTerm field grade index cell) := by
  unfold exteriorGradeQuadraticTerm
  exact ((closedDerivativeGradeQuadratic_reflected_integrableOn
    field grade index cell).integrable_indicator
      (exteriorSupportAnnulus_measurable index)).const_mul _

theorem exteriorGradeQuadraticTerm_integral_le {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade index : ℕ)
    (cell : ℝ) :
    (∫ point : SpatialPlane,
        exteriorGradeQuadraticTerm field grade index cell point) ≤
      (|coefficient index| * node index ^ grade) *
        ((7 / 5 : ℝ) * closedDerivativeGradeCoefficient grade *
          closedGradeSpatialEnergy field grade (cell : CellCircle)) := by
  unfold exteriorGradeQuadraticTerm
  rw [integral_const_mul,
    integral_indicator (exteriorSupportAnnulus_measurable index)]
  exact mul_le_mul_of_nonneg_left
    (closedDerivativeGradeQuadratic_reflected_integral_le_energy
      field grade index cell)
    (mul_nonneg (abs_nonneg _) (pow_nonneg (node_positive index).le _))

theorem exteriorGradeQuadraticTerm_integral_norm_summable {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ) (cell : ℝ) :
    Summable (fun index => ∫ point : SpatialPlane,
      ‖exteriorGradeQuadraticTerm field grade index cell point‖) := by
  let gradeEnergy : ℝ :=
    closedGradeSpatialEnergy field grade (cell : CellCircle)
  let constant : ℝ :=
    (7 / 5 : ℝ) * closedDerivativeGradeCoefficient grade * gradeEnergy
  have energyNonnegative : 0 ≤ gradeEnergy :=
    closedGradeSpatialEnergy_nonnegative field grade (cell : CellCircle)
  have constantNonnegative : 0 ≤ constant := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (closedDerivativeGradeCoefficient_nonnegative grade))
      energyNonnegative
  have majorantSummable : Summable (fun index =>
      constant * (|coefficient index| * node index ^ grade)) :=
    (coefficient_absolute_moment_summable grade).mul_left constant
  apply majorantSummable.of_norm_bounded
  intro index
  have normIdentity : (∫ point : SpatialPlane,
      ‖exteriorGradeQuadraticTerm field grade index cell point‖) =
      ∫ point : SpatialPlane,
        exteriorGradeQuadraticTerm field grade index cell point := by
    apply integral_congr_ae
    filter_upwards [] with point
    rw [Real.norm_eq_abs, abs_of_nonneg
      (exteriorGradeQuadraticTerm_nonnegative field grade index cell point)]
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun point => norm_nonneg _),
    normIdentity]
  have termBound := exteriorGradeQuadraticTerm_integral_le
    field grade index cell
  simpa only [constant, gradeEnergy, mul_assoc, mul_left_comm, mul_comm] using termBound

theorem integral_tsum_exteriorGradeQuadraticTerm_le {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ) (cell : ℝ) :
    (∫ point : SpatialPlane,
        ∑' index, exteriorGradeQuadraticTerm field grade index cell point) ≤
      ((7 / 5 : ℝ) * closedDerivativeGradeCoefficient grade *
        closedGradeSpatialEnergy field grade (cell : CellCircle)) *
        absoluteMoment grade := by
  let gradeEnergy : ℝ :=
    closedGradeSpatialEnergy field grade (cell : CellCircle)
  let constant : ℝ :=
    (7 / 5 : ℝ) * closedDerivativeGradeCoefficient grade * gradeEnergy
  have integralNormSummable :=
    exteriorGradeQuadraticTerm_integral_norm_summable field grade cell
  have termIntegralSummable : Summable (fun index =>
      ∫ point : SpatialPlane,
        exteriorGradeQuadraticTerm field grade index cell point) := by
    exact integralNormSummable.of_norm_bounded fun index =>
      norm_integral_le_integral_norm
        (exteriorGradeQuadraticTerm field grade index cell)
  have majorantSummable : Summable (fun index =>
      constant * (|coefficient index| * node index ^ grade)) :=
    (coefficient_absolute_moment_summable grade).mul_left constant
  rw [← integral_tsum_of_summable_integral_norm
    (fun index => exteriorGradeQuadraticTerm_integrable field grade index cell)
    integralNormSummable]
  calc
    (∑' index, ∫ point : SpatialPlane,
        exteriorGradeQuadraticTerm field grade index cell point) ≤
      ∑' index, constant *
        (|coefficient index| * node index ^ grade) :=
      termIntegralSummable.tsum_le_tsum
        (fun index => by
          have termBound := exteriorGradeQuadraticTerm_integral_le
            field grade index cell
          simpa only [constant, gradeEnergy, mul_assoc, mul_left_comm, mul_comm]
            using termBound)
        majorantSummable
    _ = constant * absoluteMoment grade := by
      rw [tsum_mul_left]
      rfl

theorem eventually_not_mem_exteriorSupportAnnulus (point : SpatialPlane) :
    ∃ cutoff : ℕ, ∀ index, cutoff ≤ index →
      point ∉ exteriorSupportAnnulus index := by
  by_cases outside : 1 < ‖point‖
  · have gapPositive : 0 < ‖point‖ - 1 := sub_pos.mpr outside
    have tends : Tendsto
        (fun index : ℕ => node index * (‖point‖ - 1)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const
        gapPositive
    have eventuallyLarge := tends.eventually_ge_atTop cutoffSupportWidth
    rw [eventually_atTop] at eventuallyLarge
    obtain ⟨cutoff, cutoffProperty⟩ := eventuallyLarge
    refine ⟨cutoff, fun index indexBound membership => ?_⟩
    exact (not_lt_of_ge (cutoffProperty index indexBound)) membership.2
  · exact ⟨0, fun index indexBound membership => outside membership.1⟩

noncomputable def exteriorGradeSourceTerm {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade index : ℕ)
    (cell : ℝ) (point : SpatialPlane) : ℝ :=
  (|coefficient index| * node index ^ grade) *
    (exteriorSupportAnnulus index).indicator
      (fun candidate => closedDerivativeGradePointSum field grade index
        (assembleSpatialCell candidate cell) ^ 2) point

theorem exteriorGradeSourceTerm_nonnegative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade index : ℕ)
    (cell : ℝ) (point : SpatialPlane) :
    0 ≤ exteriorGradeSourceTerm field grade index cell point := by
  unfold exteriorGradeSourceTerm
  apply mul_nonneg
  · exact mul_nonneg (abs_nonneg _)
      (pow_nonneg (node_positive index).le _)
  · by_cases membership : point ∈ exteriorSupportAnnulus index
    · rw [Set.indicator_of_mem membership]
      exact sq_nonneg _
    · simp [Set.indicator, membership]

theorem exteriorGradeSourceTerm_le_quadratic {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade index : ℕ)
    (cell : ℝ) (point : SpatialPlane) :
    exteriorGradeSourceTerm field grade index cell point ≤
      (grade + 1 : ℝ) *
        exteriorGradeQuadraticTerm field grade index cell point := by
  by_cases membership : point ∈ exteriorSupportAnnulus index
  · unfold exteriorGradeSourceTerm exteriorGradeQuadraticTerm
    rw [Set.indicator_of_mem membership, Set.indicator_of_mem membership]
    have quadraticBound := closedDerivativeGradePointSum_sq_le_quadratic
      field grade index (assembleSpatialCell point cell)
    have weightNonnegative : 0 ≤ |coefficient index| * node index ^ grade :=
      mul_nonneg (abs_nonneg _) (pow_nonneg (node_positive index).le _)
    calc
      (|coefficient index| * node index ^ grade) *
          closedDerivativeGradePointSum field grade index
            (assembleSpatialCell point cell) ^ 2 ≤
        (|coefficient index| * node index ^ grade) *
          ((grade + 1 : ℝ) *
            closedDerivativeGradeQuadratic field grade index
              (assembleSpatialCell point cell)) :=
        mul_le_mul_of_nonneg_left quadraticBound weightNonnegative
      _ = (grade + 1 : ℝ) *
          ((|coefficient index| * node index ^ grade) *
            closedDerivativeGradeQuadratic field grade index
              (assembleSpatialCell point cell)) := by ring
  · simp [exteriorGradeSourceTerm, exteriorGradeQuadraticTerm,
      Set.indicator, membership]

theorem exteriorGradeSourceTerm_summable {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ)
    (cell : ℝ) (point : SpatialPlane) :
    Summable (fun index => exteriorGradeSourceTerm field grade index cell point) := by
  obtain ⟨cutoff, tail⟩ := eventually_not_mem_exteriorSupportAnnulus point
  refine ⟨∑ index ∈ Finset.range cutoff,
    exteriorGradeSourceTerm field grade index cell point, ?_⟩
  apply hasSum_sum_of_ne_finset_zero
  intro index outsideRange
  have indexBound : cutoff ≤ index := by simpa using outsideRange
  simp [exteriorGradeSourceTerm, Set.indicator, tail index indexBound]

theorem exteriorGradeQuadraticTerm_summable {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ)
    (cell : ℝ) (point : SpatialPlane) :
    Summable (fun index => exteriorGradeQuadraticTerm field grade index cell point) := by
  obtain ⟨cutoff, tail⟩ := eventually_not_mem_exteriorSupportAnnulus point
  refine ⟨∑ index ∈ Finset.range cutoff,
    exteriorGradeQuadraticTerm field grade index cell point, ?_⟩
  apply hasSum_sum_of_ne_finset_zero
  intro index outsideRange
  have indexBound : cutoff ≤ index := by simpa using outsideRange
  simp [exteriorGradeQuadraticTerm, Set.indicator, tail index indexBound]

noncomputable def exteriorGradeSourceSeries {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ)
    (cell : ℝ) (point : SpatialPlane) : ℝ :=
  ∑' index, exteriorGradeSourceTerm field grade index cell point

noncomputable def exteriorGradeQuadraticSeries {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ)
    (cell : ℝ) (point : SpatialPlane) : ℝ :=
  ∑' index, exteriorGradeQuadraticTerm field grade index cell point

theorem tsum_exteriorGradeSourceTerm_le_quadratic {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ)
    (cell : ℝ) (point : SpatialPlane) :
    exteriorGradeSourceSeries field grade cell point ≤
      (grade + 1 : ℝ) *
        exteriorGradeQuadraticSeries field grade cell point := by
  have sourceSummable := exteriorGradeSourceTerm_summable
    field grade cell point
  have quadraticSummable := exteriorGradeQuadraticTerm_summable
    field grade cell point
  unfold exteriorGradeSourceSeries exteriorGradeQuadraticSeries
  rw [← tsum_mul_left]
  exact sourceSummable.tsum_le_tsum
    (fun index => exteriorGradeSourceTerm_le_quadratic
      field grade index cell point)
    (quadraticSummable.mul_left (grade + 1 : ℝ))

theorem exteriorHigherDerivative_norm_sq_le_quadraticSeries
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade order : ℕ) (cell : ℝ) (point : SpatialPlane)
    (upper : order ≤ grade) (outside : 1 < ‖point‖) :
    ‖exteriorHigherDerivative field order
      (assembleSpatialCell point cell)‖ ^ 2 ≤
      exteriorGradeGeometry grade (assembleSpatialCell point cell) ^ 2 *
        absoluteMoment grade * (grade + 1 : ℝ) *
          exteriorGradeQuadraticSeries field grade cell point := by
  have baseBound := exteriorHigherDerivative_norm_sq_le_grade
    field grade order (assembleSpatialCell point cell) upper (by
      change 1 < ‖planarPart (assembleSpatialCell point cell)‖
      simpa only [planarPart_assembleSpatialCell] using outside)
  have sourceIdentity :
      (∑' index,
        (|coefficient index| * node index ^ grade) *
          (exteriorSupportAnnulus index).indicator
            (fun _ => closedDerivativeGradePointSum field grade index
              (assembleSpatialCell point cell) ^ 2) point) =
      exteriorGradeSourceSeries field grade cell point := by
    unfold exteriorGradeSourceSeries
    apply tsum_congr
    intro index
    by_cases membership : point ∈ exteriorSupportAnnulus index
    · simp [exteriorGradeSourceTerm, Set.indicator, membership]
    · simp [exteriorGradeSourceTerm, Set.indicator, membership]
  rw [planarPart_assembleSpatialCell, sourceIdentity] at baseBound
  calc
    ‖exteriorHigherDerivative field order
        (assembleSpatialCell point cell)‖ ^ 2 ≤
      exteriorGradeGeometry grade (assembleSpatialCell point cell) ^ 2 *
        absoluteMoment grade *
          exteriorGradeSourceSeries field grade cell point :=
      baseBound
    _ ≤ exteriorGradeGeometry grade (assembleSpatialCell point cell) ^ 2 *
        absoluteMoment grade *
          ((grade + 1 : ℝ) *
            exteriorGradeQuadraticSeries field grade cell point) := by
      apply mul_le_mul_of_nonneg_left
      · exact tsum_exteriorGradeSourceTerm_le_quadratic
          field grade cell point
      · exact mul_nonneg (sq_nonneg _) (absoluteMoment_nonnegative grade)
    _ = exteriorGradeGeometry grade (assembleSpatialCell point cell) ^ 2 *
        absoluteMoment grade * (grade + 1 : ℝ) *
          exteriorGradeQuadraticSeries field grade cell point := by ring

noncomputable def closedDerivativeGradeQuadraticGlobalBound {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ) : ℝ :=
  ∑ order ∈ Finset.range (grade + 1),
    closedWordCoefficientSum order *
      ∑ word : MixedCartesianWord order,
        ‖spatialCellWordCoefficient word‖ *
          ‖closedMixedDerivative field order word‖ ^ 2

theorem closedDerivativeGradeQuadraticGlobalBound_nonnegative
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (grade : ℕ) :
    0 ≤ closedDerivativeGradeQuadraticGlobalBound field grade := by
  unfold closedDerivativeGradeQuadraticGlobalBound
  apply Finset.sum_nonneg
  intro order orderMembership
  exact mul_nonneg (closedWordCoefficientSum_nonnegative order)
    (Finset.sum_nonneg fun word wordMembership =>
      mul_nonneg (norm_nonneg _) (sq_nonneg _))

theorem closedDerivativeGradeQuadratic_le_globalBound {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade index : ℕ)
    (point : SpatialCell) :
    closedDerivativeGradeQuadratic field grade index point ≤
      closedDerivativeGradeQuadraticGlobalBound field grade := by
  unfold closedDerivativeGradeQuadratic
    closedDerivativeGradeQuadraticGlobalBound
  apply Finset.sum_le_sum
  intro order orderMembership
  apply mul_le_mul_of_nonneg_left _
    (closedWordCoefficientSum_nonnegative order)
  apply Finset.sum_le_sum
  intro word wordMembership
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((closedMixedDerivative field order word).norm_coe_le_norm _) 2

theorem exteriorGradeQuadraticSeries_nonnegative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ)
    (cell : ℝ) (point : SpatialPlane) :
    0 ≤ exteriorGradeQuadraticSeries field grade cell point := by
  unfold exteriorGradeQuadraticSeries
  exact tsum_nonneg fun index =>
    exteriorGradeQuadraticTerm_nonnegative field grade index cell point

theorem exteriorGradeQuadraticSeries_le_compactMajorant {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ)
    (cell : ℝ) (point : SpatialPlane) :
    exteriorGradeQuadraticSeries field grade cell point ≤
      (closedDerivativeGradeQuadraticGlobalBound field grade *
        absoluteMoment grade) *
          planarClosedGradeCollar.indicator (fun _ => (1 : ℝ)) point := by
  by_cases collarMembership : point ∈ planarClosedGradeCollar
  · rw [Set.indicator_of_mem collarMembership, mul_one]
    unfold exteriorGradeQuadraticSeries
    have majorantSummable : Summable (fun index =>
        closedDerivativeGradeQuadraticGlobalBound field grade *
          (|coefficient index| * node index ^ grade)) :=
      (coefficient_absolute_moment_summable grade).mul_left
        (closedDerivativeGradeQuadraticGlobalBound field grade)
    calc
      (∑' index, exteriorGradeQuadraticTerm field grade index cell point) ≤
        ∑' index, closedDerivativeGradeQuadraticGlobalBound field grade *
          (|coefficient index| * node index ^ grade) :=
        (exteriorGradeQuadraticTerm_summable field grade cell point).tsum_le_tsum
          (fun index => by
            by_cases supportMembership : point ∈ exteriorSupportAnnulus index
            · unfold exteriorGradeQuadraticTerm
              rw [Set.indicator_of_mem supportMembership]
              have sourceBound := closedDerivativeGradeQuadratic_le_globalBound
                field grade index (assembleSpatialCell point cell)
              have weightNonnegative :
                  0 ≤ |coefficient index| * node index ^ grade :=
                mul_nonneg (abs_nonneg _)
                  (pow_nonneg (node_positive index).le _)
              calc
                (|coefficient index| * node index ^ grade) *
                    closedDerivativeGradeQuadratic field grade index
                      (assembleSpatialCell point cell) ≤
                  (|coefficient index| * node index ^ grade) *
                    closedDerivativeGradeQuadraticGlobalBound field grade :=
                  mul_le_mul_of_nonneg_left sourceBound weightNonnegative
                _ = closedDerivativeGradeQuadraticGlobalBound field grade *
                    (|coefficient index| * node index ^ grade) := mul_comm _ _
            · simp [exteriorGradeQuadraticTerm, Set.indicator,
                supportMembership]
              exact mul_nonneg
                (closedDerivativeGradeQuadraticGlobalBound_nonnegative field grade)
                (mul_nonneg (abs_nonneg _)
                  (pow_nonneg (node_positive index).le _)))
          majorantSummable
      _ = closedDerivativeGradeQuadraticGlobalBound field grade *
          absoluteMoment grade := by
        rw [tsum_mul_left]
        rfl
  · rw [show planarClosedGradeCollar.indicator
        (fun _ => (1 : ℝ)) point = 0 by
      simp [Set.indicator, collarMembership], mul_zero]
    have seriesZero : exteriorGradeQuadraticSeries field grade cell point = 0 := by
      unfold exteriorGradeQuadraticSeries
      have termsZero : (fun index =>
          exteriorGradeQuadraticTerm field grade index cell point) = 0 := by
        funext index
        have supportNonmembership : point ∉ exteriorSupportAnnulus index :=
          fun membership => collarMembership
            (exteriorSupportAnnulus_subset_planarClosedGradeCollar index membership)
        simp [exteriorGradeQuadraticTerm, Set.indicator, supportNonmembership]
      rw [termsZero]
      change (∑' index : ℕ, (0 : ℝ)) = 0
      exact tsum_zero
    rw [seriesZero]

theorem exteriorGradeQuadraticSeries_integrable {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ) (cell : ℝ) :
    Integrable (exteriorGradeQuadraticSeries field grade cell) := by
  let majorant : SpatialPlane → ℝ := fun point =>
    (closedDerivativeGradeQuadraticGlobalBound field grade *
      absoluteMoment grade) *
        planarClosedGradeCollar.indicator (fun _ => (1 : ℝ)) point
  have majorantIntegrable : Integrable majorant := by
    unfold majorant
    exact ((continuous_const.continuousOn.integrableOn_compact
      planarClosedGradeCollar_isCompact).integrable_indicator
        planarClosedGradeCollar_isCompact.measurableSet).const_mul _
  have seriesMeasurable : AEStronglyMeasurable
      (exteriorGradeQuadraticSeries field grade cell) := by
    unfold exteriorGradeQuadraticSeries
    exact AEStronglyMeasurable.tsum fun index =>
      (exteriorGradeQuadraticTerm_integrable field grade index cell).aestronglyMeasurable
  apply majorantIntegrable.mono' seriesMeasurable
  filter_upwards [] with point
  rw [Real.norm_eq_abs, abs_of_nonneg
    (exteriorGradeQuadraticSeries_nonnegative field grade cell point)]
  exact exteriorGradeQuadraticSeries_le_compactMajorant
    field grade cell point

theorem integral_exteriorGradeQuadraticSeries_le {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ) (cell : ℝ) :
    (∫ point : SpatialPlane,
        exteriorGradeQuadraticSeries field grade cell point) ≤
      ((7 / 5 : ℝ) * closedDerivativeGradeCoefficient grade *
        closedGradeSpatialEnergy field grade (cell : CellCircle)) *
          absoluteMoment grade := by
  unfold exteriorGradeQuadraticSeries
  exact integral_tsum_exteriorGradeQuadraticTerm_le field grade cell

noncomputable def exteriorGradeGeometryBound (grade : ℕ) : ℝ :=
  Classical.choose (exists_exteriorGradeGeometry_bound grade)

theorem exteriorGradeGeometryBound_nonnegative (grade : ℕ) :
    0 ≤ exteriorGradeGeometryBound grade :=
  (Classical.choose_spec (exists_exteriorGradeGeometry_bound grade)).1

theorem exteriorGradeGeometry_le_bound (grade : ℕ)
    (point : SpatialCell) (membership : point ∈ closedGradeCollar) :
    exteriorGradeGeometry grade point ≤ exteriorGradeGeometryBound grade :=
  (Classical.choose_spec (exists_exteriorGradeGeometry_bound grade)).2
    point membership

theorem exteriorHigherDerivative_norm_sq_le_uniformQuadraticSeries
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade order : ℕ) (cell : ℝ) (point : SpatialPlane)
    (upper : order ≤ grade) (outside : 1 < ‖point‖)
    (cellMembership : cell ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    ‖exteriorHigherDerivative field order
      (assembleSpatialCell point cell)‖ ^ 2 ≤
      exteriorGradeGeometryBound grade ^ 2 * absoluteMoment grade *
        (grade + 1 : ℝ) *
          exteriorGradeQuadraticSeries field grade cell point := by
  have baseBound := exteriorHigherDerivative_norm_sq_le_quadraticSeries
    field grade order cell point upper outside
  by_cases collarMembership : point ∈ planarClosedGradeCollar
  · have assembledMembership :
        assembleSpatialCell point cell ∈ closedGradeCollar := by
      unfold closedGradeCollar
      refine ⟨(point, cell), ⟨collarMembership, cellMembership⟩, ?_⟩
      exact assembleSpatialCellCLM_apply (point, cell)
    have geometryBound := exteriorGradeGeometry_le_bound grade
      (assembleSpatialCell point cell) assembledMembership
    have geometrySquareBound :
        exteriorGradeGeometry grade (assembleSpatialCell point cell) ^ 2 ≤
          exteriorGradeGeometryBound grade ^ 2 :=
      pow_le_pow_left₀
        (exteriorGradeGeometry_nonnegative grade (assembleSpatialCell point cell))
        geometryBound 2
    have remainingNonnegative : 0 ≤ absoluteMoment grade *
        (grade + 1 : ℝ) *
          exteriorGradeQuadraticSeries field grade cell point :=
      mul_nonneg
        (mul_nonneg (absoluteMoment_nonnegative grade) (by positivity))
        (exteriorGradeQuadraticSeries_nonnegative field grade cell point)
    exact baseBound.trans (by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right geometrySquareBound remainingNonnegative)
  · have seriesZero : exteriorGradeQuadraticSeries field grade cell point = 0 := by
      unfold exteriorGradeQuadraticSeries
      have termsZero : (fun index =>
          exteriorGradeQuadraticTerm field grade index cell point) = 0 := by
        funext index
        have supportNonmembership : point ∉ exteriorSupportAnnulus index :=
          fun membership => collarMembership
            (exteriorSupportAnnulus_subset_planarClosedGradeCollar index membership)
        simp [exteriorGradeQuadraticTerm, Set.indicator, supportNonmembership]
      rw [termsZero]
      change (∑' index : ℕ, (0 : ℝ)) = 0
      exact tsum_zero
    simpa only [seriesZero, mul_zero] using baseBound

noncomputable def exteriorGradeEnergyFactor (grade : ℕ) : ℝ :=
  exteriorGradeGeometryBound grade ^ 2 * absoluteMoment grade *
    (grade + 1 : ℝ)

theorem exteriorGradeEnergyFactor_nonnegative (grade : ℕ) :
    0 ≤ exteriorGradeEnergyFactor grade := by
  unfold exteriorGradeEnergyFactor
  exact mul_nonneg
    (mul_nonneg (sq_nonneg _) (absoluteMoment_nonnegative grade)) (by positivity)

noncomputable def ambientHigherDerivativeSpatialNormSq {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ)
    (cell : ℝ) (point : SpatialPlane) : ℝ :=
  ‖ambientHigherDerivative field order (assembleSpatialCell point cell)‖ ^ 2

theorem ambientHigherDerivativeSpatialNormSq_continuous {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ) (cell : ℝ) :
    Continuous (ambientHigherDerivativeSpatialNormSq field order cell) := by
  unfold ambientHigherDerivativeSpatialNormSq
  exact (((ambientHigherDerivative_continuous field order).comp
    (assembleSpatialCellCLM.continuous.comp
      (continuous_id.prodMk continuous_const))).norm).pow 2

theorem ambientHigherDerivativeSpatialNormSq_eq_exterior
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (order : ℕ) (cell : ℝ) (point : SpatialPlane)
    (outside : point ∈ exteriorSpatialRegion) :
    ambientHigherDerivativeSpatialNormSq field order cell point =
      ‖exteriorHigherDerivative field order
        (assembleSpatialCell point cell)‖ ^ 2 := by
  unfold ambientHigherDerivativeSpatialNormSq ambientHigherDerivative
  rw [if_neg]
  rw [planarPart_assembleSpatialCell]
  exact not_le.mpr outside

theorem ambientHigherDerivative_exterior_spatial_integral_le
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade order : ℕ) (cell : ℝ) (upper : order ≤ grade)
    (cellMembership : cell ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    (∫ point in exteriorSpatialRegion,
        ambientHigherDerivativeSpatialNormSq field order cell point) ≤
      exteriorGradeEnergyFactor grade *
        (((7 / 5 : ℝ) * closedDerivativeGradeCoefficient grade *
          closedGradeSpatialEnergy field grade (cell : CellCircle)) *
            absoluteMoment grade) := by
  let upperFunction : SpatialPlane → ℝ := fun point =>
    exteriorGradeEnergyFactor grade *
      exteriorGradeQuadraticSeries field grade cell point
  have upperIntegrable : Integrable upperFunction :=
    (exteriorGradeQuadraticSeries_integrable field grade cell).const_mul _
  have upperNonnegative : ∀ point, 0 ≤ upperFunction point := fun point =>
    mul_nonneg (exteriorGradeEnergyFactor_nonnegative grade)
      (exteriorGradeQuadraticSeries_nonnegative field grade cell point)
  have lowerMeasurable : AEStronglyMeasurable
      (ambientHigherDerivativeSpatialNormSq field order cell)
      (volume.restrict exteriorSpatialRegion) :=
    (ambientHigherDerivativeSpatialNormSq_continuous field order cell).aestronglyMeasurable
      |>.mono_measure Measure.restrict_le_self
  have upperRestricted : IntegrableOn upperFunction exteriorSpatialRegion :=
    upperIntegrable.integrableOn
  have lowerIntegrable : IntegrableOn
      (ambientHigherDerivativeSpatialNormSq field order cell)
      exteriorSpatialRegion := by
    apply upperRestricted.mono' lowerMeasurable
    filter_upwards [ae_restrict_mem exteriorSpatialRegion_isOpen.measurableSet]
      with point outside
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [ambientHigherDerivativeSpatialNormSq_eq_exterior
      field order cell point outside]
    simpa only [upperFunction, exteriorGradeEnergyFactor] using
      exteriorHigherDerivative_norm_sq_le_uniformQuadraticSeries
        field grade order cell point upper outside cellMembership
  calc
    (∫ point in exteriorSpatialRegion,
        ambientHigherDerivativeSpatialNormSq field order cell point) ≤
      ∫ point in exteriorSpatialRegion, upperFunction point := by
      apply integral_mono_ae lowerIntegrable upperRestricted
      filter_upwards [ae_restrict_mem exteriorSpatialRegion_isOpen.measurableSet]
        with point outside
      rw [ambientHigherDerivativeSpatialNormSq_eq_exterior
        field order cell point outside]
      simpa only [upperFunction, exteriorGradeEnergyFactor] using
        exteriorHigherDerivative_norm_sq_le_uniformQuadraticSeries
          field grade order cell point upper outside cellMembership
    _ ≤ ∫ point : SpatialPlane, upperFunction point := by
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall upperNonnegative) upperIntegrable
    _ = exteriorGradeEnergyFactor grade *
        ∫ point : SpatialPlane,
          exteriorGradeQuadraticSeries field grade cell point := by
      rw [integral_const_mul]
    _ ≤ exteriorGradeEnergyFactor grade *
        (((7 / 5 : ℝ) * closedDerivativeGradeCoefficient grade *
          closedGradeSpatialEnergy field grade (cell : CellCircle)) *
            absoluteMoment grade) :=
      mul_le_mul_of_nonneg_left
        (integral_exteriorGradeQuadraticSeries_le field grade cell)
        (exteriorGradeEnergyFactor_nonnegative grade)

theorem closedHigherDerivativePointBound_sq_le_sourceOrder
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (order : ℕ) (point : SpatialCell) :
    closedHigherDerivativePointBound field order point ^ 2 ≤
      closedWordCoefficientSum order *
        ∑ word : MixedCartesianWord order,
          ‖spatialCellWordCoefficient word‖ *
            ‖closedMixedDerivative field order word
              (retractedDiskCell point)‖ ^ 2 := by
  have cauchy := weighted_cauchy_finset
    (Finset.univ : Finset (MixedCartesianWord order))
    (fun word => ‖spatialCellWordCoefficient word‖)
    (fun word => ‖closedMixedDerivative field order word
      (retractedDiskCell point)‖)
    (fun word _ => norm_nonneg _)
  simpa only [closedHigherDerivativePointBound,
    closedWordCoefficientSum] using cauchy

theorem closedHigherDerivative_norm_sq_le_gradeDensity
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade order : ℕ) (cell : ℝ) (point : SpatialPlane)
    (upper : order ≤ grade) :
    ‖closedHigherDerivative (order := order) field
      (assembleSpatialCell point cell)‖ ^ 2 ≤
      closedDerivativeGradeSquaredDensity field grade
        (cell : CellCircle) point := by
  have normBound := closedHigherDerivative_norm_le_pointBound
    field order (assembleSpatialCell point cell)
  have normSquareBound :
      ‖closedHigherDerivative (order := order) field
        (assembleSpatialCell point cell)‖ ^ 2 ≤
      closedHigherDerivativePointBound field order
        (assembleSpatialCell point cell) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) normBound 2
  have sourceOrderBound := closedHigherDerivativePointBound_sq_le_sourceOrder
    field order (assembleSpatialCell point cell)
  have termIdentity :
      closedWordCoefficientSum order *
          (∑ word : MixedCartesianWord order,
            ‖spatialCellWordCoefficient word‖ *
              ‖closedMixedDerivative field order word
                (retractedDiskCell (assembleSpatialCell point cell))‖ ^ 2) =
        closedWordCoefficientSum order *
          (∑ word : MixedCartesianWord order,
            ‖spatialCellWordCoefficient word‖ *
              closedMixedSquaredDensity field word
                (cell : CellCircle) point) := by
    congr 1
    apply Finset.sum_congr rfl
    intro word wordMembership
    rw [closedMixedDerivative_eq_multiIndexDerivative]
    unfold closedMixedSquaredDensity retractedDiskCell
    rw [planarPart_assembleSpatialCell]
    rfl
  rw [termIdentity] at sourceOrderBound
  calc
    ‖closedHigherDerivative (order := order) field
        (assembleSpatialCell point cell)‖ ^ 2 ≤
      closedHigherDerivativePointBound field order
        (assembleSpatialCell point cell) ^ 2 := normSquareBound
    _ ≤ closedWordCoefficientSum order *
        (∑ word : MixedCartesianWord order,
          ‖spatialCellWordCoefficient word‖ *
            closedMixedSquaredDensity field word (cell : CellCircle) point) :=
      sourceOrderBound
    _ ≤ closedDerivativeGradeSquaredDensity field grade
        (cell : CellCircle) point := by
      unfold closedDerivativeGradeSquaredDensity
      exact Finset.single_le_sum (s := Finset.range (grade + 1))
        (f := fun candidate => closedWordCoefficientSum candidate *
          ∑ word : MixedCartesianWord candidate,
            ‖spatialCellWordCoefficient word‖ *
              closedMixedSquaredDensity field word (cell : CellCircle) point)
        (fun candidate candidateMembership =>
          mul_nonneg (closedWordCoefficientSum_nonnegative candidate)
            (Finset.sum_nonneg fun word wordMembership =>
              mul_nonneg (norm_nonneg _) (sq_nonneg _)))
        (by simpa using upper)

theorem ambientHigherDerivativeSpatialNormSq_eq_closed
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (order : ℕ) (cell : ℝ) (point : SpatialPlane)
    (inside : point ∈ closedUnitDisk) :
    ambientHigherDerivativeSpatialNormSq field order cell point =
      ‖closedHigherDerivative (order := order) field
        (assembleSpatialCell point cell)‖ ^ 2 := by
  unfold ambientHigherDerivativeSpatialNormSq ambientHigherDerivative
  rw [if_pos]
  rw [planarPart_assembleSpatialCell]
  exact inside

theorem ambientHigherDerivative_closedDisk_spatial_integral_le
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade order : ℕ) (cell : ℝ) (upper : order ≤ grade) :
    (∫ point in closedUnitDisk,
        ambientHigherDerivativeSpatialNormSq field order cell point) ≤
      closedDerivativeGradeCoefficient grade *
        closedGradeSpatialEnergy field grade (cell : CellCircle) := by
  have diskCompact : IsCompact closedUnitDisk := by
    rw [closedUnitDisk_eq_closedBall]
    exact isCompact_closedBall (0 : SpatialPlane) 1
  have lowerIntegrable : IntegrableOn
      (ambientHigherDerivativeSpatialNormSq field order cell) closedUnitDisk :=
    (ambientHigherDerivativeSpatialNormSq_continuous field order cell).continuousOn
      |>.integrableOn_compact diskCompact
  have upperIntegrable : IntegrableOn
      (closedDerivativeGradeSquaredDensity field grade (cell : CellCircle))
      closedUnitDisk :=
    (closedDerivativeGradeSquaredDensity_continuous
      field grade (cell : CellCircle)).continuousOn
        |>.integrableOn_compact diskCompact
  calc
    (∫ point in closedUnitDisk,
        ambientHigherDerivativeSpatialNormSq field order cell point) ≤
      ∫ point in closedUnitDisk,
        closedDerivativeGradeSquaredDensity field grade
          (cell : CellCircle) point := by
      apply integral_mono_ae lowerIntegrable upperIntegrable
      filter_upwards [ae_restrict_mem (by
        rw [closedUnitDisk_eq_closedBall]
        exact Metric.isClosed_closedBall.measurableSet)] with point inside
      rw [ambientHigherDerivativeSpatialNormSq_eq_closed
        field order cell point inside]
      exact closedHigherDerivative_norm_sq_le_gradeDensity
        field grade order cell point upper
    _ ≤ closedDerivativeGradeCoefficient grade *
        closedGradeSpatialEnergy field grade (cell : CellCircle) :=
      closedDerivativeGradeSquaredDensity_integral_le
        field grade (cell : CellCircle)

theorem ambientHigherDerivativeSpatialNormSq_integrableOn_exterior
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade order : ℕ) (cell : ℝ) (upper : order ≤ grade)
    (cellMembership : cell ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    IntegrableOn (ambientHigherDerivativeSpatialNormSq field order cell)
      exteriorSpatialRegion := by
  let upperFunction : SpatialPlane → ℝ := fun point =>
    exteriorGradeEnergyFactor grade *
      exteriorGradeQuadraticSeries field grade cell point
  have upperIntegrable : Integrable upperFunction :=
    (exteriorGradeQuadraticSeries_integrable field grade cell).const_mul _
  have lowerMeasurable : AEStronglyMeasurable
      (ambientHigherDerivativeSpatialNormSq field order cell)
      (volume.restrict exteriorSpatialRegion) :=
    (ambientHigherDerivativeSpatialNormSq_continuous field order cell).aestronglyMeasurable
      |>.mono_measure Measure.restrict_le_self
  apply upperIntegrable.integrableOn.mono' lowerMeasurable
  filter_upwards [ae_restrict_mem exteriorSpatialRegion_isOpen.measurableSet]
    with point outside
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [ambientHigherDerivativeSpatialNormSq_eq_exterior
    field order cell point outside]
  simpa only [upperFunction, exteriorGradeEnergyFactor] using
    exteriorHigherDerivative_norm_sq_le_uniformQuadraticSeries
      field grade order cell point upper outside cellMembership

theorem closedUnitDisk_union_exteriorSpatialRegion :
    closedUnitDisk ∪ exteriorSpatialRegion = (Set.univ : Set SpatialPlane) := by
  ext point
  change (‖point‖ ≤ 1 ∨ 1 < ‖point‖) ↔ _
  simp [le_or_gt]

theorem closedUnitDisk_disjoint_exteriorSpatialRegion :
    Disjoint closedUnitDisk exteriorSpatialRegion := by
  rw [Set.disjoint_left]
  intro point inside outside
  change ‖point‖ ≤ 1 at inside
  change 1 < ‖point‖ at outside
  exact (not_lt_of_ge inside) outside

noncomputable def ambientGradeEnergyFactor (grade : ℕ) : ℝ :=
  closedDerivativeGradeCoefficient grade +
    exteriorGradeEnergyFactor grade *
      ((7 / 5 : ℝ) * closedDerivativeGradeCoefficient grade) *
        absoluteMoment grade

theorem ambientGradeEnergyFactor_nonnegative (grade : ℕ) :
    0 ≤ ambientGradeEnergyFactor grade := by
  unfold ambientGradeEnergyFactor
  exact add_nonneg (closedDerivativeGradeCoefficient_nonnegative grade)
    (mul_nonneg
      (mul_nonneg (exteriorGradeEnergyFactor_nonnegative grade)
        (mul_nonneg (by norm_num)
          (closedDerivativeGradeCoefficient_nonnegative grade)))
      (absoluteMoment_nonnegative grade))

theorem ambientHigherDerivativeSpatialNormSq_integrable
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade order : ℕ) (cell : ℝ) (upper : order ≤ grade)
    (cellMembership : cell ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    Integrable (ambientHigherDerivativeSpatialNormSq field order cell) := by
  have diskIntegrable : IntegrableOn
      (ambientHigherDerivativeSpatialNormSq field order cell) closedUnitDisk :=
    (ambientHigherDerivativeSpatialNormSq_continuous field order cell).continuousOn
      |>.integrableOn_compact (by
        rw [closedUnitDisk_eq_closedBall]
        exact isCompact_closedBall (0 : SpatialPlane) 1)
  have exteriorIntegrable :=
    ambientHigherDerivativeSpatialNormSq_integrableOn_exterior
      field grade order cell upper cellMembership
  have unionIntegrable := diskIntegrable.union exteriorIntegrable
  rw [closedUnitDisk_union_exteriorSpatialRegion] at unionIntegrable
  simpa only [integrableOn_univ] using unionIntegrable

theorem ambientHigherDerivative_spatial_integral_le
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade order : ℕ) (cell : ℝ) (upper : order ≤ grade)
    (cellMembership : cell ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    (∫ point : SpatialPlane,
        ambientHigherDerivativeSpatialNormSq field order cell point) ≤
      ambientGradeEnergyFactor grade *
        closedGradeSpatialEnergy field grade (cell : CellCircle) := by
  have diskIntegrable : IntegrableOn
      (ambientHigherDerivativeSpatialNormSq field order cell) closedUnitDisk :=
    (ambientHigherDerivativeSpatialNormSq_continuous field order cell).continuousOn
      |>.integrableOn_compact (by
        rw [closedUnitDisk_eq_closedBall]
        exact isCompact_closedBall (0 : SpatialPlane) 1)
  have exteriorIntegrable :=
    ambientHigherDerivativeSpatialNormSq_integrableOn_exterior
      field grade order cell upper cellMembership
  have unionIdentity := setIntegral_union
    closedUnitDisk_disjoint_exteriorSpatialRegion
    exteriorSpatialRegion_isOpen.measurableSet
    diskIntegrable exteriorIntegrable
  rw [closedUnitDisk_union_exteriorSpatialRegion, setIntegral_univ] at unionIdentity
  rw [unionIdentity]
  calc
    (∫ point in closedUnitDisk,
        ambientHigherDerivativeSpatialNormSq field order cell point) +
      ∫ point in exteriorSpatialRegion,
        ambientHigherDerivativeSpatialNormSq field order cell point ≤
      closedDerivativeGradeCoefficient grade *
          closedGradeSpatialEnergy field grade (cell : CellCircle) +
        exteriorGradeEnergyFactor grade *
          (((7 / 5 : ℝ) * closedDerivativeGradeCoefficient grade *
            closedGradeSpatialEnergy field grade (cell : CellCircle)) *
              absoluteMoment grade) :=
      add_le_add
        (ambientHigherDerivative_closedDisk_spatial_integral_le
          field grade order cell upper)
        (ambientHigherDerivative_exterior_spatial_integral_le
          field grade order cell upper cellMembership)
    _ = ambientGradeEnergyFactor grade *
        closedGradeSpatialEnergy field grade (cell : CellCircle) := by
      unfold ambientGradeEnergyFactor
      ring

theorem spatialCellBasis_norm (coordinate : Fin 3) :
    ‖spatialCellBasis coordinate‖ = 1 := by
  change ‖WithLp.toLp 2 (Pi.single coordinate (1 : ℝ) : Fin 3 → ℝ)‖ = 1
  simp

theorem mixedCartesianDerivative_norm_le_ambientHigherDerivative
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (point : SpatialCell) :
    ‖mixedCartesianDerivative order word
      (ambientExtensionCellLift field) point‖ ≤
      ‖ambientHigherDerivative field order point‖ := by
  rw [mixedCartesianDerivative,
    ← ambientHigherDerivative_eq_iteratedFDeriv_ambient field order point]
  simpa only [spatialCellBasis_norm, Finset.prod_const_one, mul_one] using
    (ambientHigherDerivative field order point).le_opNorm
      (fun position => spatialCellBasis (word position))

theorem mixedCartesianDerivative_norm_sq_le_ambientHigherDerivative
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (point : SpatialCell) :
    ‖mixedCartesianDerivative order word
      (ambientExtensionCellLift field) point‖ ^ 2 ≤
      ‖ambientHigherDerivative field order point‖ ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _)
    (mixedCartesianDerivative_norm_le_ambientHigherDerivative field word point) 2

theorem periodized_index_squared_eq_ambient_mixed
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (index : DiskCellMultiIndex) (cell : ℝ) (point : SpatialPlane)
    (membership : point ∈ fundamentalIocSquare) :
    torusMultiDerivativeSquaredLift (periodizedExtension field) index
        (cell : CellCircle) point =
      ‖mixedCartesianDerivative (diskCellOrder index)
        (diskCellMultiIndexWord index) (ambientExtensionCellLift field)
          (assembleSpatialCell point cell)‖ ^ 2 := by
  unfold torusMultiDerivativeSquaredLift torusDiskCellMultiDerivative
  congr 2
  simpa [torusCellPoint, assembleSpatialCell] using
    periodized_mixedDerivative_eq_ambient_on_fundamental
      field (diskCellMultiIndexWord index) point cell membership

theorem periodized_index_fundamental_spatial_integral_le
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade : ℕ) (index : DiskCellMultiIndex)
    (indexMembership : index ∈ diskCellMultiIndices grade)
    (cell : ℝ) (cellMembership : cell ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    (∫ point in fundamentalIocSquare,
        torusMultiDerivativeSquaredLift (periodizedExtension field) index
          (cell : CellCircle) point) ≤
      ambientGradeEnergyFactor grade *
        closedGradeSpatialEnergy field grade (cell : CellCircle) := by
  have orderUpper : diskCellOrder index ≤ grade :=
    (Finset.mem_filter.mp indexMembership).2
  have torusIntegrable : IntegrableOn
      (torusMultiDerivativeSquaredLift (periodizedExtension field) index
        (cell : CellCircle)) fundamentalIocSquare :=
    (torusMultiDerivativeSquaredLift_continuous
      (periodizedExtension field) index (cell : CellCircle)).continuousOn
        |>.integrableOn_compact fundamentalIccSquare_isCompact
        |>.mono_set fundamentalIocSquare_subset_Icc
  have ambientIntegrable := ambientHigherDerivativeSpatialNormSq_integrable
    field grade (diskCellOrder index) cell orderUpper cellMembership
  calc
    (∫ point in fundamentalIocSquare,
        torusMultiDerivativeSquaredLift (periodizedExtension field) index
          (cell : CellCircle) point) ≤
      ∫ point in fundamentalIocSquare,
        ambientHigherDerivativeSpatialNormSq field (diskCellOrder index)
          cell point := by
      apply integral_mono_ae torusIntegrable ambientIntegrable.integrableOn
      filter_upwards [ae_restrict_mem fundamentalIocSquare_measurable]
        with point pointMembership
      rw [periodized_index_squared_eq_ambient_mixed
        field index cell point pointMembership]
      exact mixedCartesianDerivative_norm_sq_le_ambientHigherDerivative
        field (diskCellMultiIndexWord index) (assembleSpatialCell point cell)
    _ ≤ ∫ point : SpatialPlane,
        ambientHigherDerivativeSpatialNormSq field (diskCellOrder index)
          cell point := by
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun point => sq_nonneg _) ambientIntegrable
    _ ≤ ambientGradeEnergyFactor grade *
        closedGradeSpatialEnergy field grade (cell : CellCircle) :=
      ambientHigherDerivative_spatial_integral_le
        field grade (diskCellOrder index) cell orderUpper cellMembership

theorem periodized_index_spatial_energy_le
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade : ℕ) (index : DiskCellMultiIndex)
    (indexMembership : index ∈ diskCellMultiIndices grade)
    (cell : ℝ) (cellMembership : cell ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    (∫ second : SpatialCircle, ∫ first : SpatialCircle,
        ‖torusDiskCellMultiDerivative (periodizedExtension field) index
          ((first, second), (cell : CellCircle))‖ ^ 2
        ∂spatialProbabilityMeasure ∂spatialProbabilityMeasure) ≤
      (1 / 256 : ℝ) * ambientGradeEnergyFactor grade *
        closedGradeSpatialEnergy field grade (cell : CellCircle) := by
  rw [integral_two_spatialProbabilityMeasures]
  have liftIntegrable : IntegrableOn
      (torusMultiDerivativeSquaredLift (periodizedExtension field) index
        (cell : CellCircle)) fundamentalIocSquare :=
    (torusMultiDerivativeSquaredLift_continuous
      (periodizedExtension field) index (cell : CellCircle)).continuousOn
        |>.integrableOn_compact fundamentalIccSquare_isCompact
        |>.mono_set fundamentalIocSquare_subset_Icc
  have iteratedIdentity :
      (∫ second in Ioc (-2 : ℝ) 2,
        ∫ first in Ioc (-2 : ℝ) 2,
          ‖torusDiskCellMultiDerivative (periodizedExtension field) index
            (((first : SpatialCircle), (second : SpatialCircle)),
              (cell : CellCircle))‖ ^ 2) =
      ∫ point in fundamentalIocSquare,
        torusMultiDerivativeSquaredLift (periodizedExtension field) index
          (cell : CellCircle) point := by
    symm
    simpa [torusMultiDerivativeSquaredLift] using
      integral_fundamentalIocSquare_eq_iterated
        (torusMultiDerivativeSquaredLift (periodizedExtension field) index
          (cell : CellCircle)) liftIntegrable
  rw [iteratedIdentity]
  change (1 / 256 : ℝ) *
      (∫ point in fundamentalIocSquare,
        torusMultiDerivativeSquaredLift (periodizedExtension field) index
          (cell : CellCircle) point) ≤ _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (periodized_index_fundamental_spatial_integral_le
      field grade index indexMembership cell cellMembership)
    (by norm_num : 0 ≤ (1 / 256 : ℝ))

theorem periodized_index_spatial_energy_circle_le
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade : ℕ) (index : DiskCellMultiIndex)
    (indexMembership : index ∈ diskCellMultiIndices grade)
    (cell : CellCircle) :
    (∫ second : SpatialCircle, ∫ first : SpatialCircle,
        ‖torusDiskCellMultiDerivative (periodizedExtension field) index
          ((first, second), cell)‖ ^ 2
        ∂spatialProbabilityMeasure ∂spatialProbabilityMeasure) ≤
      (1 / 256 : ℝ) * ambientGradeEnergyFactor grade *
        closedGradeSpatialEnergy field grade cell := by
  let representative : ℝ :=
    (AddCircle.equivIco (2 * Real.pi) 0 cell).val
  have representativeMembership : representative ∈
      Set.Icc (0 : ℝ) (2 * Real.pi) := by
    constructor
    · simpa only [representative] using
        (AddCircle.equivIco (2 * Real.pi) 0 cell).property.1
    · simpa only [representative, zero_add] using
        (AddCircle.equivIco (2 * Real.pi) 0 cell).property.2.le
  have representativeEquality : (representative : CellCircle) = cell := by
    exact AddCircle.coe_equivIco
  simpa only [representativeEquality] using
    periodized_index_spatial_energy_le field grade index indexMembership
      representative representativeMembership

noncomputable def closedIndexSpatialEnergy {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : DiskCellMultiIndex)
    (cell : CellCircle) : ℝ :=
  ∫ point : SpatialPlane,
    ‖closedDiskLift
      (fun diskPoint => closedDiskCellMultiDerivative field index
        (diskPoint, cell)) point‖ ^ 2

theorem closedIndexSpatialEnergy_integrable {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : DiskCellMultiIndex) :
    Integrable (closedIndexSpatialEnergy field index) cellProbabilityMeasure := by
  let continuousJoint : CellCircle × SpatialPlane → ℝ := fun input =>
    ‖closedDiskCellMultiDerivative field index
      (radialRetraction input.2, input.1)‖ ^ 2
  have jointContinuous : Continuous continuousJoint := by
    unfold continuousJoint
    exact (((closedDiskCellMultiDerivative field index).continuous.comp
      ((continuous_radialRetraction.comp continuous_snd).prodMk
        continuous_fst)).norm).pow 2
  let supportSet : Set (CellCircle × SpatialPlane) :=
    Set.univ ×ˢ closedUnitDisk
  have supportCompact : IsCompact supportSet := by
    unfold supportSet
    rw [closedUnitDisk_eq_closedBall]
    exact isCompact_univ.prod (isCompact_closedBall (0 : SpatialPlane) 1)
  have supportMeasurable : MeasurableSet supportSet := by
    exact supportCompact.measurableSet
  have indicatorIntegrable : Integrable
      (supportSet.indicator continuousJoint)
      (cellProbabilityMeasure.prod volume) :=
    (jointContinuous.continuousOn.integrableOn_compact
      supportCompact).integrable_indicator supportMeasurable
  have jointEquality :
      (fun input : CellCircle × SpatialPlane =>
        ‖closedDiskLift
          (fun diskPoint => closedDiskCellMultiDerivative field index
            (diskPoint, input.1)) input.2‖ ^ 2) =
      supportSet.indicator continuousJoint := by
    funext input
    by_cases membership : input.2 ∈ closedUnitDisk
    · rw [closedDiskLift, dif_pos membership,
        Set.indicator_of_mem (show input ∈ supportSet by
          exact ⟨Set.mem_univ _, membership⟩)]
      unfold continuousJoint
      have retractionEquality : radialRetraction input.2 =
          (⟨input.2, membership⟩ : ClosedDisk) := by
        exact Subtype.ext (radialRetraction_val_of_mem input.2 membership)
      rw [retractionEquality]
    · simp [closedDiskLift, Set.indicator, supportSet, membership]
  have diskJointIntegrable : Integrable
      (fun input : CellCircle × SpatialPlane =>
        ‖closedDiskLift
          (fun diskPoint => closedDiskCellMultiDerivative field index
            (diskPoint, input.1)) input.2‖ ^ 2)
      (cellProbabilityMeasure.prod volume) := by
    rw [jointEquality]
    exact indicatorIntegrable
  exact diskJointIntegrable.integral_prod_left

theorem closedGradeSpatialEnergy_integrable {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ) :
    Integrable (closedGradeSpatialEnergy field grade) cellProbabilityMeasure := by
  unfold closedGradeSpatialEnergy
  exact integrable_finsetSum (diskCellMultiIndices grade)
    (fun index indexMembership => closedIndexSpatialEnergy_integrable field index)

theorem closedGradeSpatialEnergy_integral_eq_diskDerivativeEnergy
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (grade : ℕ) :
    (∫ cell : CellCircle, closedGradeSpatialEnergy field grade cell
      ∂cellProbabilityMeasure) = diskDerivativeEnergy grade field := by
  unfold closedGradeSpatialEnergy diskDerivativeEnergy
  rw [integral_finsetSum]
  intro index indexMembership
  exact closedIndexSpatialEnergy_integrable field index

theorem periodized_index_cell_energy_le
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade : ℕ) (index : DiskCellMultiIndex)
    (indexMembership : index ∈ diskCellMultiIndices grade) :
    (∫ cell : CellCircle,
        torusSpatialEnergy (periodizedExtension field) index cell
        ∂cellProbabilityMeasure) ≤
      ((1 / 256 : ℝ) * ambientGradeEnergyFactor grade) *
        diskDerivativeEnergy grade field := by
  have lowerIntegrable := torusSpatialEnergy_integrable
    (periodizedExtension field) index
  have upperIntegrable :=
    (closedGradeSpatialEnergy_integrable field grade).const_mul
      ((1 / 256 : ℝ) * ambientGradeEnergyFactor grade)
  calc
    (∫ cell : CellCircle,
        torusSpatialEnergy (periodizedExtension field) index cell
        ∂cellProbabilityMeasure) ≤
      ∫ cell : CellCircle,
        ((1 / 256 : ℝ) * ambientGradeEnergyFactor grade) *
          closedGradeSpatialEnergy field grade cell
        ∂cellProbabilityMeasure := by
      apply integral_mono lowerIntegrable upperIntegrable
      intro cell
      unfold torusSpatialEnergy
      exact periodized_index_spatial_energy_circle_le
        field grade index indexMembership cell
    _ = ((1 / 256 : ℝ) * ambientGradeEnergyFactor grade) *
        (∫ cell : CellCircle, closedGradeSpatialEnergy field grade cell
          ∂cellProbabilityMeasure) := by
      rw [integral_const_mul]
    _ = ((1 / 256 : ℝ) * ambientGradeEnergyFactor grade) *
        diskDerivativeEnergy grade field := by
      rw [closedGradeSpatialEnergy_integral_eq_diskDerivativeEnergy]

noncomputable def periodizedGradeEnergyFactor (grade : ℕ) : ℝ :=
  (diskCellMultiIndices grade).card *
    ((1 / 256 : ℝ) * ambientGradeEnergyFactor grade)

theorem periodizedGradeEnergyFactor_nonnegative (grade : ℕ) :
    0 ≤ periodizedGradeEnergyFactor grade := by
  unfold periodizedGradeEnergyFactor
  exact mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (by norm_num) (ambientGradeEnergyFactor_nonnegative grade))

theorem torusDerivativeEnergy_periodizedExtension_le
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (grade : ℕ) :
    torusDerivativeEnergy grade (periodizedExtension field) ≤
      periodizedGradeEnergyFactor grade * diskDerivativeEnergy grade field := by
  unfold torusDerivativeEnergy
  calc
    (∑ index ∈ diskCellMultiIndices grade,
        ∫ cell : CellCircle, ∫ second : SpatialCircle,
          ∫ first : SpatialCircle,
            ‖torusDiskCellMultiDerivative (periodizedExtension field) index
              ((first, second), cell)‖ ^ 2
            ∂spatialProbabilityMeasure ∂spatialProbabilityMeasure
          ∂cellProbabilityMeasure) ≤
      ∑ index ∈ diskCellMultiIndices grade,
        ((1 / 256 : ℝ) * ambientGradeEnergyFactor grade) *
          diskDerivativeEnergy grade field := by
      apply Finset.sum_le_sum
      intro index indexMembership
      change (∫ cell : CellCircle,
          torusSpatialEnergy (periodizedExtension field) index cell
          ∂cellProbabilityMeasure) ≤ _
      exact periodized_index_cell_energy_le
        field grade index indexMembership
    _ = periodizedGradeEnergyFactor grade *
        diskDerivativeEnergy grade field := by
      unfold periodizedGradeEnergyFactor
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

end Grad.DiskExtension.Operator
