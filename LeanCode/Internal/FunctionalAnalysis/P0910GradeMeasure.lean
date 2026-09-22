import P0910CellCommutation
import Mathlib.Analysis.SpecialFunctions.PolarCoord

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets

local instance p0910SpatialProbabilityFinite :
    IsFiniteMeasure spatialProbabilityMeasure := by
  unfold spatialProbabilityMeasure
  exact Measure.smul_finite AddCircle.haarAddCircle (by simp)

local instance p0910CellProbabilityFinite :
    IsFiniteMeasure cellProbabilityMeasure := by
  unfold cellProbabilityMeasure
  apply Measure.smul_finite AddCircle.haarAddCircle
  rw [ENNReal.inv_ne_top]
  exact (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) Real.pi_pos)).ne'

theorem integral_spatialProbabilityMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : SpatialCircle → E) :
    ∫ point, function point ∂spatialProbabilityMeasure =
      (1 / 16 : ℝ) •
        ∫ coordinate in Ioc (-2 : ℝ) 2,
          function (coordinate : SpatialCircle) := by
  rw [spatialProbabilityMeasure, integral_smul_measure,
    AddCircle.integral_haarAddCircle]
  rw [← AddCircle.integral_preimage (4 : ℝ) (-2 : ℝ) function]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal]
  · rw [smul_smul]
    norm_num
  · norm_num

theorem integral_cellProbabilityMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : CellCircle → E) :
    ∫ point, function point ∂cellProbabilityMeasure =
      ((2 * Real.pi : ℝ)⁻¹ ^ 2) •
        ∫ coordinate in Ioc (0 : ℝ) (2 * Real.pi),
          function (coordinate : CellCircle) := by
  rw [cellProbabilityMeasure, integral_smul_measure,
    AddCircle.integral_haarAddCircle]
  rw [← AddCircle.integral_preimage (2 * Real.pi) (0 : ℝ) function]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal]
  · rw [smul_smul]
    congr 1
    ring
    simp
  · positivity

def fundamentalIocSquare : Set SpatialPlane :=
  {point | point 0 ∈ Ioc (-2 : ℝ) 2 ∧ point 1 ∈ Ioc (-2 : ℝ) 2}

def fundamentalIccSquare : Set SpatialPlane :=
  {point | point 0 ∈ Icc (-2 : ℝ) 2 ∧ point 1 ∈ Icc (-2 : ℝ) 2}

def spatialPlaneCoordinateHomeomorph : SpatialPlane ≃ₜ (ℝ × ℝ) where
  toFun point := (point 0, point 1)
  invFun point := WithLp.toLp 2 ![point.1, point.2]
  left_inv point := by
    ext coordinate
    fin_cases coordinate <;> rfl
  right_inv point := by
    ext <;> rfl
  continuous_toFun := by
    exact (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 => ℝ) 0).prodMk
      (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 => ℝ) 1)
  continuous_invFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    fun_prop

theorem fundamentalIccSquare_isCompact : IsCompact fundamentalIccSquare := by
  have imageEquality : fundamentalIccSquare =
      spatialPlaneCoordinateHomeomorph.symm ''
        (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) := by
    ext point
    constructor
    · intro membership
      refine ⟨(point 0, point 1), membership, ?_⟩
      apply spatialPlaneCoordinateHomeomorph.injective
      rfl
    · rintro ⟨pair, membership, rfl⟩
      exact membership
  rw [imageEquality]
  exact (isCompact_Icc.prod isCompact_Icc).image
    spatialPlaneCoordinateHomeomorph.symm.continuous

theorem fundamentalIocSquare_subset_Icc :
    fundamentalIocSquare ⊆ fundamentalIccSquare := by
  intro point membership
  exact ⟨⟨membership.1.1.le, membership.1.2⟩,
    ⟨membership.2.1.le, membership.2.2⟩⟩

theorem closedUnitDisk_subset_fundamentalIocSquare :
    closedUnitDisk ⊆ fundamentalIocSquare := by
  intro point membership
  have firstBound := spatialPlane_coordinate_abs_le_norm point 0
  have secondBound := spatialPlane_coordinate_abs_le_norm point 1
  change ‖point‖ ≤ 1 at membership
  constructor <;> constructor <;> linarith [le_abs_self (point 0),
    neg_abs_le (point 0), le_abs_self (point 1), neg_abs_le (point 1)]

theorem fundamentalIocSquare_measurable : MeasurableSet fundamentalIocSquare := by
  exact @MeasurableSet.inter SpatialPlane _ _ _
    (measurableSet_Ioc.preimage
      (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 => ℝ) 0).measurable)
    (measurableSet_Ioc.preimage
      (PiLp.continuous_apply (p := 2) (fun _ : Fin 2 => ℝ) 1).measurable)

theorem integral_fundamentalIocSquare_eq_iterated
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : SpatialPlane → E)
    (integrable : IntegrableOn function fundamentalIocSquare) :
    ∫ point in fundamentalIocSquare, function point =
      ∫ second in Ioc (-2 : ℝ) 2,
        ∫ first in Ioc (-2 : ℝ) 2,
          function (WithLp.toLp 2 ![first, second]) := by
  classical
  rw [← integral_indicator fundamentalIocSquare_measurable]
  let coordinateEquiv : SpatialPlane ≃ᵐ (ℝ × ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans
      MeasurableEquiv.finTwoArrow
  have coordinateMeasurePreserving : MeasurePreserving coordinateEquiv
      (volume : Measure SpatialPlane) ((volume : Measure ℝ).prod volume) := by
    exact (volume_preserving_finTwoArrow ℝ).comp
      (PiLp.volume_preserving_ofLp (Fin 2))
  have transformed := coordinateMeasurePreserving.integral_comp'
    (fun point : ℝ × ℝ =>
      fundamentalIocSquare.indicator function (coordinateEquiv.symm point))
  have planeEquality :
      (∫ point : SpatialPlane,
        fundamentalIocSquare.indicator function point) =
      ∫ point : ℝ × ℝ,
        fundamentalIocSquare.indicator function
          (coordinateEquiv.symm point)
          ∂((volume : Measure ℝ).prod volume) := by
    simpa using transformed
  rw [planeEquality]
  have coordinateSymm :
      (fun point : ℝ × ℝ => coordinateEquiv.symm point) =
      (fun point : ℝ × ℝ =>
        WithLp.toLp 2 ![point.1, point.2]) := by
    rfl
  have integrandEquality :
      (fun point : ℝ × ℝ =>
        fundamentalIocSquare.indicator function
          (coordinateEquiv.symm point)) =
      (fun point : ℝ × ℝ =>
        fundamentalIocSquare.indicator function
          (WithLp.toLp 2 ![point.1, point.2])) := by
    funext point
    rw [congrFun coordinateSymm point]
  rw [integrandEquality]
  have pairIntegrable : IntegrableOn
      (fun point : ℝ × ℝ =>
        function (WithLp.toLp 2 ![point.1, point.2]))
      (Ioc (-2 : ℝ) 2 ×ˢ Ioc (-2 : ℝ) 2)
      ((volume : Measure ℝ).prod volume) := by
    have transported :=
      (coordinateMeasurePreserving.symm.integrableOn_comp_preimage
        coordinateEquiv.symm.measurableEmbedding).2 integrable
    change IntegrableOn
      (fun point : ℝ × ℝ =>
        function (WithLp.toLp 2 ![point.1, point.2]))
      {point | point.1 ∈ Ioc (-2 : ℝ) 2 ∧
        point.2 ∈ Ioc (-2 : ℝ) 2}
      ((volume : Measure ℝ).prod volume)
    simpa [Function.comp_def, fundamentalIocSquare, coordinateEquiv] using transported
  have indicatorEquality :
      (fun point : ℝ × ℝ =>
        fundamentalIocSquare.indicator function
          (WithLp.toLp 2 ![point.1, point.2])) =
      (Ioc (-2 : ℝ) 2 ×ˢ Ioc (-2 : ℝ) 2).indicator
        (fun point : ℝ × ℝ =>
          function (WithLp.toLp 2 ![point.1, point.2])) := by
    funext point
    have membershipEquality :
        WithLp.toLp 2 ![point.1, point.2] ∈ fundamentalIocSquare ↔
          point ∈ Ioc (-2 : ℝ) 2 ×ˢ Ioc (-2 : ℝ) 2 := by
      change ((point.1 ∈ Ioc (-2 : ℝ) 2 ∧
        point.2 ∈ Ioc (-2 : ℝ) 2) ↔ _)
      rfl
    simp only [Set.indicator]
    rw [if_congr membershipEquality rfl rfl]
  rw [indicatorEquality,
    integral_indicator (μ := ((volume : Measure ℝ).prod volume))
      (measurableSet_Ioc.prod measurableSet_Ioc)]
  rw [setIntegral_prod _ pairIntegrable]
  have restrictedIntegrable : Integrable
      (fun point : ℝ × ℝ =>
        function (WithLp.toLp 2 ![point.1, point.2]))
      ((volume.restrict (Ioc (-2 : ℝ) 2)).prod
        (volume.restrict (Ioc (-2 : ℝ) 2))) := by
    rw [Measure.prod_restrict]
    exact pairIntegrable
  exact integral_integral_swap restrictedIntegrable

theorem integral_two_spatialProbabilityMeasures
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : SpatialCircle → SpatialCircle → E) :
    ∫ second, ∫ first, function first second
        ∂spatialProbabilityMeasure ∂spatialProbabilityMeasure =
      (1 / 256 : ℝ) •
        ∫ second in Ioc (-2 : ℝ) 2,
          ∫ first in Ioc (-2 : ℝ) 2,
            function (first : SpatialCircle) (second : SpatialCircle) := by
  rw [integral_spatialProbabilityMeasure]
  simp_rw [integral_spatialProbabilityMeasure]
  rw [integral_smul]
  rw [smul_smul]
  norm_num

def torusMultiDerivativeSquaredLift {dimension : ℕ}
    (field : TorusSmoothField dimension) (index : DiskCellMultiIndex)
    (cell : CellCircle) (point : SpatialPlane) : ℝ :=
  ‖torusDiskCellMultiDerivative field index
    (((point 0 : SpatialCircle), (point 1 : SpatialCircle)), cell)‖ ^ 2

theorem torusMultiDerivativeSquaredLift_continuous {dimension : ℕ}
    (field : TorusSmoothField dimension) (index : DiskCellMultiIndex)
    (cell : CellCircle) :
    Continuous (torusMultiDerivativeSquaredLift field index cell) := by
  apply Continuous.pow
  apply Continuous.norm
  exact (torusDiskCellMultiDerivative field index).continuous.comp (by
    fun_prop)

theorem restriction_spatial_integral_le_fundamental
    {dimension : ℕ} (field : TorusSmoothField dimension)
    (index : DiskCellMultiIndex) (cell : CellCircle) :
    (∫ point : SpatialPlane,
      ‖closedDiskLift
        (fun diskPoint => closedDiskCellMultiDerivative
          (torusRestriction field) index (diskPoint, cell)) point‖ ^ 2) ≤
      ∫ second in Ioc (-2 : ℝ) 2,
        ∫ first in Ioc (-2 : ℝ) 2,
          ‖torusDiskCellMultiDerivative field index
            (((first : SpatialCircle), (second : SpatialCircle)), cell)‖ ^ 2 := by
  let integrand := torusMultiDerivativeSquaredLift field index cell
  have integrandContinuous : Continuous integrand :=
    torusMultiDerivativeSquaredLift_continuous field index cell
  have integrableClosed : IntegrableOn integrand fundamentalIccSquare :=
    integrandContinuous.continuousOn.integrableOn_compact
      fundamentalIccSquare_isCompact
  have integrableFundamental : IntegrableOn integrand fundamentalIocSquare :=
    integrableClosed.mono_set fundamentalIocSquare_subset_Icc
  have diskSubsetClosed : closedUnitDisk ⊆ fundamentalIccSquare :=
    closedUnitDisk_subset_fundamentalIocSquare.trans
      fundamentalIocSquare_subset_Icc
  have liftSquaredEquality :
      (fun point : SpatialPlane =>
        ‖closedDiskLift
          (fun diskPoint => closedDiskCellMultiDerivative
            (torusRestriction field) index (diskPoint, cell)) point‖ ^ 2) =
      closedUnitDisk.indicator integrand := by
    classical
    funext point
    by_cases membership : point ∈ closedUnitDisk
    · rw [closedDiskLift, dif_pos membership,
        Set.indicator_of_mem membership]
      rw [closedDiskCellMultiDerivative, torusRestriction_derivative]
      rfl
    · simp [closedDiskLift, membership]
  rw [liftSquaredEquality,
    integral_indicator (by
      rw [closedUnitDisk_eq_closedBall]
      exact Metric.isClosed_closedBall.measurableSet)]
  calc
    (∫ point in closedUnitDisk, integrand point) ≤
        ∫ point in fundamentalIocSquare, integrand point := by
      exact setIntegral_mono_set integrableFundamental
        (Filter.Eventually.of_forall fun point => sq_nonneg _)
        (Filter.Eventually.of_forall closedUnitDisk_subset_fundamentalIocSquare)
    _ = ∫ second in Ioc (-2 : ℝ) 2,
          ∫ first in Ioc (-2 : ℝ) 2,
            ‖torusDiskCellMultiDerivative field index
              (((first : SpatialCircle), (second : SpatialCircle)), cell)‖ ^ 2 := by
      rw [integral_fundamentalIocSquare_eq_iterated
        integrand integrableFundamental]
      rfl

theorem restriction_spatial_integral_le_torus
    {dimension : ℕ} (field : TorusSmoothField dimension)
    (index : DiskCellMultiIndex) (cell : CellCircle) :
    (∫ point : SpatialPlane,
      ‖closedDiskLift
        (fun diskPoint => closedDiskCellMultiDerivative
          (torusRestriction field) index (diskPoint, cell)) point‖ ^ 2) ≤
      256 *
        ∫ second : SpatialCircle, ∫ first : SpatialCircle,
          ‖torusDiskCellMultiDerivative field index
            ((first, second), cell)‖ ^ 2
          ∂spatialProbabilityMeasure ∂spatialProbabilityMeasure := by
  rw [integral_two_spatialProbabilityMeasures]
  simpa [smul_eq_mul] using
    restriction_spatial_integral_le_fundamental field index cell

def restrictionDiskSpatialEnergy {dimension : ℕ}
    (field : TorusSmoothField dimension) (index : DiskCellMultiIndex)
    (cell : CellCircle) : ℝ :=
  ∫ point : SpatialPlane,
    ‖closedDiskLift
      (fun diskPoint => closedDiskCellMultiDerivative
        (torusRestriction field) index (diskPoint, cell)) point‖ ^ 2

def torusSpatialEnergy {dimension : ℕ}
    (field : TorusSmoothField dimension) (index : DiskCellMultiIndex)
    (cell : CellCircle) : ℝ :=
  ∫ second : SpatialCircle, ∫ first : SpatialCircle,
    ‖torusDiskCellMultiDerivative field index ((first, second), cell)‖ ^ 2
      ∂spatialProbabilityMeasure ∂spatialProbabilityMeasure

theorem restrictionDiskSpatialEnergy_integrable {dimension : ℕ}
    (field : TorusSmoothField dimension) (index : DiskCellMultiIndex) :
    Integrable (restrictionDiskSpatialEnergy field index)
      cellProbabilityMeasure := by
  let continuousJoint : CellCircle × SpatialPlane → ℝ := fun input =>
    torusMultiDerivativeSquaredLift field index input.1 input.2
  have jointContinuous : Continuous continuousJoint := by
    apply Continuous.pow
    apply Continuous.norm
    exact (torusDiskCellMultiDerivative field index).continuous.comp (by
      fun_prop)
  let supportSet : Set (CellCircle × SpatialPlane) :=
    Set.univ ×ˢ closedUnitDisk
  have supportCompact : IsCompact supportSet := by
    dsimp only [supportSet]
    rw [closedUnitDisk_eq_closedBall]
    exact isCompact_univ.prod (isCompact_closedBall (0 : SpatialPlane) 1)
  have supportMeasurable : MeasurableSet supportSet := by
    dsimp only [supportSet]
    rw [closedUnitDisk_eq_closedBall]
    exact MeasurableSet.univ.prod Metric.isClosed_closedBall.measurableSet
  have indicatorIntegrable : Integrable
      (supportSet.indicator continuousJoint)
      (cellProbabilityMeasure.prod volume) :=
    (jointContinuous.continuousOn.integrableOn_compact
      supportCompact).integrable_indicator supportMeasurable
  have jointEquality :
      (fun input : CellCircle × SpatialPlane =>
        ‖closedDiskLift
          (fun diskPoint => closedDiskCellMultiDerivative
            (torusRestriction field) index (diskPoint, input.1)) input.2‖ ^ 2) =
      supportSet.indicator continuousJoint := by
    classical
    funext input
    by_cases membership : input.2 ∈ closedUnitDisk
    · rw [closedDiskLift, dif_pos membership,
        Set.indicator_of_mem (show input ∈ supportSet by
          exact ⟨Set.mem_univ _, membership⟩)]
      rw [closedDiskCellMultiDerivative, torusRestriction_derivative]
      rfl
    · simp [closedDiskLift, membership, supportSet]
  have diskJointIntegrable : Integrable
      (fun input : CellCircle × SpatialPlane =>
        ‖closedDiskLift
          (fun diskPoint => closedDiskCellMultiDerivative
            (torusRestriction field) index (diskPoint, input.1)) input.2‖ ^ 2)
      (cellProbabilityMeasure.prod volume) := by
    rw [jointEquality]
    exact indicatorIntegrable
  exact diskJointIntegrable.integral_prod_left

theorem torusSpatialEnergy_integrable {dimension : ℕ}
    (field : TorusSmoothField dimension) (index : DiskCellMultiIndex) :
    Integrable (torusSpatialEnergy field index) cellProbabilityMeasure := by
  let joint : CellCircle × (SpatialCircle × SpatialCircle) → ℝ := fun input =>
    ‖torusDiskCellMultiDerivative field index
      ((input.2.2, input.2.1), input.1)‖ ^ 2
  have jointContinuous : Continuous joint := by
    apply Continuous.pow
    apply Continuous.norm
    exact (torusDiskCellMultiDerivative field index).continuous.comp (by
      fun_prop)
  have jointIntegrable : Integrable joint
      (cellProbabilityMeasure.prod
        (spatialProbabilityMeasure.prod spatialProbabilityMeasure)) :=
    by
      simpa using jointContinuous.continuousOn.integrableOn_compact
        (μ := cellProbabilityMeasure.prod
          (spatialProbabilityMeasure.prod spatialProbabilityMeasure))
        isCompact_univ
  have productEnergyIntegrable := jointIntegrable.integral_prod_left
  have energyEquality :
      torusSpatialEnergy field index =
        (fun cell => ∫ pair : SpatialCircle × SpatialCircle,
          joint (cell, pair)
          ∂(spatialProbabilityMeasure.prod spatialProbabilityMeasure)) := by
    funext cell
    have sliceContinuous : Continuous
        (fun pair : SpatialCircle × SpatialCircle => joint (cell, pair)) := by
      exact jointContinuous.comp
        ((continuous_const : Continuous
          (fun _ : SpatialCircle × SpatialCircle => cell)).prodMk continuous_id)
    have sliceIntegrable : Integrable (fun pair => joint (cell, pair))
        (spatialProbabilityMeasure.prod spatialProbabilityMeasure) :=
      by
        simpa using sliceContinuous.continuousOn.integrableOn_compact
          (μ := spatialProbabilityMeasure.prod spatialProbabilityMeasure)
          isCompact_univ
    rw [torusSpatialEnergy, integral_prod _ sliceIntegrable]
  rw [energyEquality]
  exact productEnergyIntegrable

theorem restriction_index_energy_le_torus
    {dimension : ℕ} (field : TorusSmoothField dimension)
    (index : DiskCellMultiIndex) :
    (∫ cell : CellCircle, restrictionDiskSpatialEnergy field index cell
      ∂cellProbabilityMeasure) ≤
      256 * ∫ cell : CellCircle, torusSpatialEnergy field index cell
        ∂cellProbabilityMeasure := by
  rw [← integral_const_mul]
  exact integral_mono
    (restrictionDiskSpatialEnergy_integrable field index)
    ((torusSpatialEnergy_integrable field index).const_mul 256)
    (fun cell => restriction_spatial_integral_le_torus field index cell)

theorem diskDerivativeEnergy_restriction_le
    (grade : ℕ) {dimension : ℕ} (field : TorusSmoothField dimension) :
    diskDerivativeEnergy grade (torusRestriction field) ≤
      256 * torusDerivativeEnergy grade field := by
  rw [diskDerivativeEnergy, torusDerivativeEnergy]
  calc
    (∑ index ∈ diskCellMultiIndices grade,
        ∫ cell : CellCircle,
          ∫ point : SpatialPlane,
            ‖closedDiskLift
              (fun diskPoint => closedDiskCellMultiDerivative
                (torusRestriction field) index (diskPoint, cell)) point‖ ^ 2
            ∂volume ∂cellProbabilityMeasure) ≤
      ∑ index ∈ diskCellMultiIndices grade,
        256 * ∫ cell : CellCircle, torusSpatialEnergy field index cell
          ∂cellProbabilityMeasure := by
      apply Finset.sum_le_sum
      intro index _
      exact restriction_index_energy_le_torus field index
    _ = 256 * ∑ index ∈ diskCellMultiIndices grade,
        ∫ cell : CellCircle, torusSpatialEnergy field index cell
          ∂cellProbabilityMeasure := by
      simp_rw [Finset.mul_sum]
    _ = 256 * ∑ index ∈ diskCellMultiIndices grade,
        ∫ cell : CellCircle, ∫ second : SpatialCircle,
          ∫ first : SpatialCircle,
            ‖torusDiskCellMultiDerivative field index
              ((first, second), cell)‖ ^ 2
          ∂spatialProbabilityMeasure ∂spatialProbabilityMeasure
          ∂cellProbabilityMeasure := by
      rfl

theorem torusDerivativeEnergy_nonnegative
    (grade : ℕ) {dimension : ℕ} (field : TorusSmoothField dimension) :
    0 ≤ torusDerivativeEnergy grade field := by
  rw [torusDerivativeEnergy]
  apply Finset.sum_nonneg
  intro index _
  apply integral_nonneg
  intro cell
  apply integral_nonneg
  intro second
  apply integral_nonneg
  intro first
  exact sq_nonneg _

theorem diskDerivativeEnergy_nonnegative
    (grade : ℕ) {dimension : ℕ} (field : DiskCellClosedJet dimension) :
    0 ≤ diskDerivativeEnergy grade field := by
  rw [diskDerivativeEnergy]
  apply Finset.sum_nonneg
  intro index _
  apply integral_nonneg
  intro cell
  apply integral_nonneg
  intro point
  exact sq_nonneg _

theorem diskDerivativeGrade_restriction_le
    (grade : ℕ) {dimension : ℕ} (field : TorusSmoothField dimension) :
    diskDerivativeGrade grade (torusRestriction field) ≤
      16 * torusDerivativeGrade grade field := by
  rw [diskDerivativeGrade, torusDerivativeGrade]
  calc
    Real.sqrt (diskDerivativeEnergy grade (torusRestriction field)) ≤
        Real.sqrt (256 * torusDerivativeEnergy grade field) :=
      Real.sqrt_le_sqrt (diskDerivativeEnergy_restriction_le grade field)
    _ = 16 * Real.sqrt (torusDerivativeEnergy grade field) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 256)]
      rw [show Real.sqrt 256 = 16 by
        exact (Real.sqrt_eq_iff_mul_self_eq
          (by norm_num) (by norm_num)).2 (by norm_num)]

end Grad.DiskExtension.Operator
