import FP17ClosedJet
import Mathlib.Topology.CompactOpen
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section

set_option maxHeartbeats 500000

open Filter Set MeasureTheory
open scoped ContDiff Topology

namespace Grad.CartesianState

open Grad.ClosedJets

local instance fp17InverseCellPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

/-- The joint continuous Fourier integrand, with circle variable first so
compact-open currying produces a continuous family of disk maps. -/
def diskCellFourierJoint {dimension : ℕ}
    (value : C(DiskCellDomain, ComplexEuclidean dimension)) (cell : ℤ) :
    C(CellCircle × ClosedDisk, ComplexEuclidean dimension) where
  toFun point :=
    fourier (-cell) point.1 • value (point.2, point.1)
  continuous_toFun :=
    ((fourier (-cell)).continuous.comp continuous_fst).smul
      (value.continuous.comp (continuous_snd.prodMk continuous_fst))

/-- The same integrand as a continuous circle-indexed family in the Banach
space of continuous disk maps. -/
def diskCellFourierFamily {dimension : ℕ}
    (value : C(DiskCellDomain, ComplexEuclidean dimension)) (cell : ℤ) :
    C(CellCircle, C(ClosedDisk, ComplexEuclidean dimension)) :=
  (diskCellFourierJoint value cell).curry

theorem diskCellFourierFamily_integrable {dimension : ℕ}
    (value : C(DiskCellDomain, ComplexEuclidean dimension)) (cell : ℤ) :
    Integrable (diskCellFourierFamily value cell) AddCircle.haarAddCircle := by
  simpa only [integrableOn_univ] using
    (ContinuousOn.integrableOn_compact isCompact_univ
      (diskCellFourierFamily value cell).continuous.continuousOn)

/-- Cell Fourier coefficient as an actual continuous map of the closed disk.
Continuity is obtained by integrating in the Banach space of continuous maps. -/
def diskCellFourierValue {dimension : ℕ}
    (value : C(DiskCellDomain, ComplexEuclidean dimension)) (cell : ℤ) :
    C(ClosedDisk, ComplexEuclidean dimension) :=
  ∫ circle : CellCircle, diskCellFourierFamily value cell circle
    ∂AddCircle.haarAddCircle

theorem diskCellFourierValue_apply {dimension : ℕ}
    (value : C(DiskCellDomain, ComplexEuclidean dimension)) (cell : ℤ)
    (point : ClosedDisk) :
    diskCellFourierValue value cell point =
      fourierCoeff (T := 2 * Real.pi)
        (fun circle : CellCircle => value (point, circle)) cell := by
  rw [diskCellFourierValue, ContinuousMap.integral_apply
    (diskCellFourierFamily_integrable value cell) point]
  rfl

/-- Restrict a disk-cell continuous value to one fixed cell circle. -/
def diskCellSlice {dimension : ℕ}
    (value : C(DiskCellDomain, ComplexEuclidean dimension))
    (circle : CellCircle) : C(ClosedDisk, ComplexEuclidean dimension) :=
  value.comp
    { toFun := fun point => (point, circle)
      continuous_toFun := continuous_id.prodMk continuous_const }

@[simp] theorem diskCellSlice_apply {dimension : ℕ}
    (value : C(DiskCellDomain, ComplexEuclidean dimension))
    (circle : CellCircle) (point : ClosedDisk) :
    diskCellSlice value circle point = value (point, circle) := rfl

private def fp17PlanarEmbeddingLinear : SpatialPlane →ₗ[ℝ] SpatialCell where
  toFun point := assembleSpatialCell point 0
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> simp [assembleSpatialCell]
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;> simp [assembleSpatialCell]

private noncomputable def fp17PlanarEmbeddingCLM :
    SpatialPlane →L[ℝ] SpatialCell :=
  fp17PlanarEmbeddingLinear.toContinuousLinearMap

@[simp] private theorem fp17PlanarEmbeddingCLM_apply
    (point : SpatialPlane) :
    fp17PlanarEmbeddingCLM point = assembleSpatialCell point 0 := rfl

@[simp] private theorem fp17PlanarEmbeddingCLM_basis
    (coordinate : Fin 2) :
    fp17PlanarEmbeddingCLM (spatialBasis coordinate) =
      spatialCellBasis (fp17PlanarCoordinate coordinate) := by
  ext component
  fin_cases coordinate <;> fin_cases component <;> rfl

private theorem assembleSpatialCell_hasFDerivAt
    (point : SpatialPlane) (cell : ℝ) :
    HasFDerivAt (fun candidate : SpatialPlane =>
      assembleSpatialCell candidate cell) fp17PlanarEmbeddingCLM point := by
  have functionIdentity :
      (fun candidate : SpatialPlane => assembleSpatialCell candidate cell) =
        fun candidate => fp17PlanarEmbeddingCLM candidate +
          assembleSpatialCell 0 cell := by
    funext candidate
    ext coordinate
    fin_cases coordinate <;> simp [assembleSpatialCell]
  rw [functionIdentity]
  exact fp17PlanarEmbeddingCLM.hasFDerivAt.add_const _

private theorem closedDiskLift_diskCellSlice_eq_fieldLift
    {dimension : ℕ} (value : C(DiskCellDomain, ComplexEuclidean dimension))
    (circle : CellCircle) :
    ∃ cell : ℝ, (cell : CellCircle) = circle ∧
      Set.EqOn (closedDiskLift (diskCellSlice value circle))
        (fun point => diskCellLift value (assembleSpatialCell point cell))
        openUnitDisk := by
  obtain ⟨cell, rfl⟩ := QuotientAddGroup.mk_surjective circle
  refine ⟨cell, rfl, ?_⟩
  intro point membership
  have closedMembership := openDiskMembershipClosed point membership
  have cylinderMembership :
      assembleSpatialCell point cell ∈ openUnitCylinder := by
    change ‖planarPart (assembleSpatialCell point cell)‖ < 1
    simpa [openUnitDisk] using membership
  rw [closedDiskLift, dif_pos closedMembership]
  simp only [diskCellLift, dif_pos
    (openCylinderMembershipClosed _ cylinderMembership)]
  change value
      ((⟨point, closedMembership⟩ : ClosedDisk), (cell : CellCircle)) =
    value (diskCellPoint (assembleSpatialCell point cell)
      (openCylinderMembershipClosed _ cylinderMembership))
  congr 1
  exact (diskCellPoint_assembleSpatialCell
    (⟨point, closedMembership⟩ : ClosedDisk) cell membership).symm

def fp17LiftPlanarWord {order : ℕ} (word : CartesianWord order) :
    MixedCartesianWord order :=
  fun position => fp17PlanarCoordinate (word position)

private noncomputable def fp17PlanarCoordinateCLM (coordinate : Fin 2) :
    SpatialPlane →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 2 => ℝ) coordinate

private def closedMixedPlanarDerivativeCLM
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (point : SpatialPlane)
    (circle : CellCircle) :
    SpatialPlane →L[ℝ] ComplexEuclidean dimension :=
  (ContinuousLinearMap.smulRightL ℝ SpatialPlane
      (ComplexEuclidean dimension)) (fp17PlanarCoordinateCLM 0)
        (closedMixedDerivative field (order + 1)
          (Fin.cons (fp17PlanarCoordinate 0) word)
            (ambientClosedDisk point, circle)) +
    (ContinuousLinearMap.smulRightL ℝ SpatialPlane
      (ComplexEuclidean dimension)) (fp17PlanarCoordinateCLM 1)
        (closedMixedDerivative field (order + 1)
          (Fin.cons (fp17PlanarCoordinate 1) word)
            (ambientClosedDisk point, circle))

private theorem closedMixedDerivative_slice_eq_actual
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (circle : CellCircle) :
    ∃ cell : ℝ, (cell : CellCircle) = circle ∧
      Set.EqOn
        (closedDiskLift
          (diskCellSlice (closedMixedDerivative field order word) circle))
        (fun point => mixedCartesianDerivative order word
          (diskCellLift field.value) (assembleSpatialCell point cell))
        openUnitDisk := by
  obtain ⟨cell, cellEquality, sliceEquality⟩ :=
    closedDiskLift_diskCellSlice_eq_fieldLift
      (closedMixedDerivative field order word) circle
  refine ⟨cell, cellEquality, ?_⟩
  intro point membership
  rw [sliceEquality membership]
  have cylinderMembership :
      assembleSpatialCell point cell ∈ openUnitCylinder := by
    change ‖planarPart (assembleSpatialCell point cell)‖ < 1
    simpa [openUnitDisk] using membership
  simp only [diskCellLift, dif_pos
    (openCylinderMembershipClosed _ cylinderMembership)]
  rw [closedMixedDerivative_spec field order word _ cylinderMembership]

private theorem actualMixedDerivative_planar_fderiv_basis
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℝ)
    (point : SpatialPlane) (membership : point ∈ openUnitDisk)
    (coordinate : Fin 2) :
    fderiv ℝ
        (fun candidate => mixedCartesianDerivative order word
          (diskCellLift field.value) (assembleSpatialCell candidate cell)) point
          (spatialBasis coordinate) =
      mixedCartesianDerivative (order + 1)
        (Fin.cons (fp17PlanarCoordinate coordinate) word)
          (diskCellLift field.value) (assembleSpatialCell point cell) := by
  have cylinderMembership :
      assembleSpatialCell point cell ∈ openUnitCylinder := by
    change ‖planarPart (assembleSpatialCell point cell)‖ < 1
    simpa [openUnitDisk] using membership
  have smoothAt := (field.smoothInterior _ cylinderMembership).contDiffAt
    (openUnitCylinder_isOpen.mem_nhds cylinderMembership)
  have tensorDifferentiable := smoothAt.differentiableAt_iteratedFDeriv
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl order)
  have evaluatedDifferentiable : DifferentiableAt ℝ
      (fun ambient => mixedCartesianDerivative order word
        (diskCellLift field.value) ambient)
      (assembleSpatialCell point cell) :=
    tensorDifferentiable.continuousMultilinear_apply_const
      (fun position => spatialCellBasis (word position))
  have composed := evaluatedDifferentiable.hasFDerivAt.comp point
    (assembleSpatialCell_hasFDerivAt point cell)
  change fderiv ℝ
      ((fun ambient => mixedCartesianDerivative order word
        (diskCellLift field.value) ambient) ∘
          fun candidate => assembleSpatialCell candidate cell) point
        (spatialBasis coordinate) = _
  rw [composed.fderiv, ContinuousLinearMap.comp_apply,
    fp17PlanarEmbeddingCLM_basis]
  have successor := tensorDifferentiable.iteratedFDeriv_succ_apply_left'
    (m := Fin.cons (spatialCellBasis (fp17PlanarCoordinate coordinate))
      (fun position => spatialCellBasis (word position)))
  exact successor.symm

private theorem closedMixedDerivative_slice_fderiv_basis
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (circle : CellCircle)
    (point : SpatialPlane) (membership : point ∈ openUnitDisk)
    (coordinate : Fin 2) :
    fderiv ℝ
        (closedDiskLift
          (diskCellSlice (closedMixedDerivative field order word) circle)) point
          (spatialBasis coordinate) =
      closedMixedDerivative field (order + 1)
        (Fin.cons (fp17PlanarCoordinate coordinate) word)
          (ambientClosedDisk point, circle) := by
  obtain ⟨cell, cellEquality, localAgreement⟩ :=
    closedMixedDerivative_slice_eq_actual field word circle
  subst circle
  have eventuallyAgreement :
      closedDiskLift
          (diskCellSlice (closedMixedDerivative field order word)
            (cell : CellCircle)) =ᶠ[𝓝 point]
        (fun candidate => mixedCartesianDerivative order word
          (diskCellLift field.value) (assembleSpatialCell candidate cell)) :=
    Filter.eventually_of_mem
      (openUnitDisk_isOpen.mem_nhds membership) localAgreement
  rw [eventuallyAgreement.fderiv_eq]
  rw [actualMixedDerivative_planar_fderiv_basis field word cell point
    membership coordinate]
  have cylinderMembership :
      assembleSpatialCell point cell ∈ openUnitCylinder := by
    change ‖planarPart (assembleSpatialCell point cell)‖ < 1
    simpa [openUnitDisk] using membership
  rw [← closedMixedDerivative_spec field (order + 1)
    (Fin.cons (fp17PlanarCoordinate coordinate) word) _ cylinderMembership]
  have pointIdentity :
      diskCellPoint (assembleSpatialCell point cell)
          (openCylinderMembershipClosed _ cylinderMembership) =
        (ambientClosedDisk point, (cell : CellCircle)) := by
    apply Prod.ext
    · apply Subtype.ext
      change planarPart (assembleSpatialCell point cell) =
        (ambientClosedDisk point).val
      rw [planarPart_assembleSpatialCell,
        ambientClosedDisk_val_of_mem
          (openDiskMembershipClosed point membership)]
    · rfl
  rw [pointIdentity]

private theorem closedMixedDerivative_slice_hasFDerivAt
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (circle : CellCircle)
    (point : SpatialPlane) (membership : point ∈ openUnitDisk) :
    HasFDerivAt
      (closedDiskLift
        (diskCellSlice (closedMixedDerivative field order word) circle))
      (closedMixedPlanarDerivativeCLM field word point circle) point := by
  obtain ⟨cell, _cellEquality, localAgreement⟩ :=
    closedMixedDerivative_slice_eq_actual field word circle
  have cylinderMembership :
      assembleSpatialCell point cell ∈ openUnitCylinder := by
    change ‖planarPart (assembleSpatialCell point cell)‖ < 1
    simpa [openUnitDisk] using membership
  have smoothAt := (field.smoothInterior _ cylinderMembership).contDiffAt
    (openUnitCylinder_isOpen.mem_nhds cylinderMembership)
  have tensorDifferentiable := smoothAt.differentiableAt_iteratedFDeriv
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl order)
  have evaluatedDifferentiable : DifferentiableAt ℝ
      (fun ambient => mixedCartesianDerivative order word
        (diskCellLift field.value) ambient)
      (assembleSpatialCell point cell) :=
    tensorDifferentiable.continuousMultilinear_apply_const
      (fun position => spatialCellBasis (word position))
  have actualDifferentiable : DifferentiableAt ℝ
      (fun candidate => mixedCartesianDerivative order word
        (diskCellLift field.value) (assembleSpatialCell candidate cell)) point :=
    by
      change DifferentiableAt ℝ
        ((fun ambient => mixedCartesianDerivative order word
          (diskCellLift field.value) ambient) ∘
            fun candidate => assembleSpatialCell candidate cell) point
      exact evaluatedDifferentiable.comp point
        (assembleSpatialCell_hasFDerivAt point cell).differentiableAt
  have localEventually :
      closedDiskLift
          (diskCellSlice (closedMixedDerivative field order word) circle) =ᶠ[𝓝 point]
        (fun candidate => mixedCartesianDerivative order word
          (diskCellLift field.value) (assembleSpatialCell candidate cell)) :=
    Filter.eventually_of_mem (openUnitDisk_isOpen.mem_nhds membership)
      localAgreement
  have sliceDifferentiable : DifferentiableAt ℝ
      (closedDiskLift
        (diskCellSlice (closedMixedDerivative field order word) circle)) point :=
    actualDifferentiable.congr_of_eventuallyEq localEventually
  have derivativeIdentity :
      fderiv ℝ
          (closedDiskLift
            (diskCellSlice (closedMixedDerivative field order word) circle))
          point = closedMixedPlanarDerivativeCLM field word point circle := by
    apply ContinuousLinearMap.ext
    intro direction
    have planeExpansion :
        (∑ coordinate : Fin 2,
          (direction coordinate) • spatialBasis coordinate) = direction := by
      ext component
      fin_cases component <;>
        simp [Fin.sum_univ_two, spatialBasis]
    calc
      fderiv ℝ
          (closedDiskLift
            (diskCellSlice (closedMixedDerivative field order word) circle))
          point direction =
          ∑ coordinate : Fin 2, (direction coordinate) •
            fderiv ℝ
              (closedDiskLift
                (diskCellSlice (closedMixedDerivative field order word) circle))
              point (spatialBasis coordinate) := by
        calc
          _ = fderiv ℝ
              (closedDiskLift
                (diskCellSlice (closedMixedDerivative field order word) circle))
              point (∑ coordinate : Fin 2,
                (direction coordinate) • spatialBasis coordinate) := by
            rw [planeExpansion]
          _ = _ := by
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro coordinate _
            rw [map_smul]
      _ = ∑ coordinate : Fin 2, (direction coordinate) •
          closedMixedPlanarDerivativeCLM field word point circle
            (spatialBasis coordinate) := by
        apply Finset.sum_congr rfl
        intro coordinate _
        congr 1
        rw [closedMixedDerivative_slice_fderiv_basis field word circle point
          membership coordinate]
        fin_cases coordinate <;>
          simp [closedMixedPlanarDerivativeCLM,
            fp17PlanarCoordinateCLM, spatialBasis]
      _ = closedMixedPlanarDerivativeCLM field word point circle direction := by
        symm
        calc
          _ = closedMixedPlanarDerivativeCLM field word point circle
              (∑ coordinate : Fin 2,
                (direction coordinate) • spatialBasis coordinate) := by
            rw [planeExpansion]
          _ = _ := by
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro coordinate _
            rw [map_smul]
  rw [← derivativeIdentity]
  exact sliceDifferentiable.hasFDerivAt

private theorem spatialPlaneLinear_norm_le_sum_basis
    {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (linear : SpatialPlane →L[ℝ] Value) :
    ‖linear‖ ≤ ∑ coordinate : Fin 2,
      ‖linear (spatialBasis coordinate)‖ := by
  apply linear.opNorm_le_bound
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro point
  have planeExpansion :
      (∑ coordinate : Fin 2,
        (point coordinate) • spatialBasis coordinate) = point := by
    ext component
    fin_cases component <;>
      simp [Fin.sum_univ_two, spatialBasis]
  calc
    ‖linear point‖ = ‖linear (∑ coordinate : Fin 2,
        (point coordinate) • spatialBasis coordinate)‖ := by rw [planeExpansion]
    _ = ‖∑ coordinate : Fin 2,
        (point coordinate) • linear (spatialBasis coordinate)‖ := by
      rw [map_sum]
      apply congrArg norm
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [map_smul]
    _ ≤ ∑ coordinate : Fin 2,
        ‖(point coordinate) • linear (spatialBasis coordinate)‖ :=
      norm_sum_le _ _
    _ = ∑ coordinate : Fin 2,
        |point coordinate| * ‖linear (spatialBasis coordinate)‖ := by
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ coordinate : Fin 2,
        ‖point‖ * ‖linear (spatialBasis coordinate)‖ := by
      apply Finset.sum_le_sum
      intro coordinate _
      exact mul_le_mul_of_nonneg_right
        (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le point coordinate)
        (norm_nonneg _)
    _ = (∑ coordinate : Fin 2,
        ‖linear (spatialBasis coordinate)‖) * ‖point‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro coordinate _
      ring

private theorem closedMixedPlanarDerivativeCLM_norm_le
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (point : SpatialPlane)
    (circle : CellCircle) :
    ‖closedMixedPlanarDerivativeCLM field word point circle‖ ≤
      ‖closedMixedDerivative field (order + 1)
        (Fin.cons (fp17PlanarCoordinate 0) word)‖ +
      ‖closedMixedDerivative field (order + 1)
        (Fin.cons (fp17PlanarCoordinate 1) word)‖ := by
  calc
    ‖closedMixedPlanarDerivativeCLM field word point circle‖ ≤
        ∑ coordinate : Fin 2,
          ‖closedMixedPlanarDerivativeCLM field word point circle
            (spatialBasis coordinate)‖ :=
      spatialPlaneLinear_norm_le_sum_basis _
    _ = ‖closedMixedDerivative field (order + 1)
          (Fin.cons (fp17PlanarCoordinate 0) word)
            (ambientClosedDisk point, circle)‖ +
        ‖closedMixedDerivative field (order + 1)
          (Fin.cons (fp17PlanarCoordinate 1) word)
            (ambientClosedDisk point, circle)‖ := by
      simp [Fin.sum_univ_two, closedMixedPlanarDerivativeCLM,
        fp17PlanarCoordinateCLM, spatialBasis]
    _ ≤ ‖closedMixedDerivative field (order + 1)
          (Fin.cons (fp17PlanarCoordinate 0) word)‖ +
        ‖closedMixedDerivative field (order + 1)
          (Fin.cons (fp17PlanarCoordinate 1) word)‖ :=
      add_le_add
        ((closedMixedDerivative field (order + 1)
          (Fin.cons (fp17PlanarCoordinate 0) word)).norm_coe_le_norm _)
        ((closedMixedDerivative field (order + 1)
          (Fin.cons (fp17PlanarCoordinate 1) word)).norm_coe_le_norm _)

private def diskCellFourierParameter
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ)
    (point : SpatialPlane) (circle : CellCircle) :
    ComplexEuclidean dimension :=
  fourier (-cell) circle •
    closedDiskLift
      (diskCellSlice (closedMixedDerivative field order word) circle) point

private def diskCellFourierParameterDerivative
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ)
    (point : SpatialPlane) (circle : CellCircle) :
    SpatialPlane →L[ℝ] ComplexEuclidean dimension :=
  fourier (-cell) circle •
    closedMixedPlanarDerivativeCLM field word point circle

private def diskCellFourierDerivativeBound
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) : ℝ :=
  ‖closedMixedDerivative field (order + 1)
      (Fin.cons (fp17PlanarCoordinate 0) word)‖ +
    ‖closedMixedDerivative field (order + 1)
      (Fin.cons (fp17PlanarCoordinate 1) word)‖

private theorem diskCellFourierParameter_continuous_circle
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ)
    (point : SpatialPlane) (membership : point ∈ openUnitDisk) :
    Continuous (diskCellFourierParameter field word cell point) := by
  have closedMembership := openDiskMembershipClosed point membership
  have valueContinuous : Continuous
      (fun circle : CellCircle =>
        closedMixedDerivative field order word
          ((⟨point, closedMembership⟩ : ClosedDisk), circle)) :=
    (closedMixedDerivative field order word).continuous.comp
      (continuous_const.prodMk continuous_id)
  change Continuous (fun circle : CellCircle =>
    fourier (-cell) circle •
      closedDiskLift
        (diskCellSlice (closedMixedDerivative field order word) circle) point)
  have productContinuous :=
    (fourier (-cell)).continuous.smul valueContinuous
  apply productContinuous.congr
  intro circle
  simp only [closedDiskLift, dif_pos closedMembership,
    diskCellSlice_apply]
  rfl

private theorem diskCellFourierParameterDerivative_continuous_circle
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ)
    (point : SpatialPlane) :
    Continuous (diskCellFourierParameterDerivative field word cell point) := by
  unfold diskCellFourierParameterDerivative closedMixedPlanarDerivativeCLM
  fun_prop

private theorem diskCellFourierParameterDerivative_norm_le
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ)
    (point : SpatialPlane) (circle : CellCircle) :
    ‖diskCellFourierParameterDerivative field word cell point circle‖ ≤
      diskCellFourierDerivativeBound field word := by
  rw [diskCellFourierParameterDerivative,
    norm_smul, show ‖fourier (-cell) circle‖ = 1 by exact Circle.norm_coe _,
    one_mul]
  exact closedMixedPlanarDerivativeCLM_norm_le field word point circle

private theorem diskCellFourierParameter_hasFDerivAt
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ)
    (point : SpatialPlane) (membership : point ∈ openUnitDisk)
    (circle : CellCircle) :
    HasFDerivAt (fun candidate =>
      diskCellFourierParameter field word cell candidate circle)
      (diskCellFourierParameterDerivative field word cell point circle) point := by
  have scaled :=
    (closedMixedDerivative_slice_hasFDerivAt field word circle point
      membership).const_smul (fourier (-cell) circle)
  change HasFDerivAt
    ((fourier (-cell) circle) •
      closedDiskLift
        (diskCellSlice (closedMixedDerivative field order word) circle))
    ((fourier (-cell) circle) •
      closedMixedPlanarDerivativeCLM field word point circle) point
  exact scaled

private theorem diskCellFourierParameterDerivative_basis
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ)
    (point : SpatialPlane) (circle : CellCircle) (coordinate : Fin 2) :
    diskCellFourierParameterDerivative field word cell point circle
        (spatialBasis coordinate) =
      fourier (-cell) circle •
        closedMixedDerivative field (order + 1)
          (Fin.cons (fp17PlanarCoordinate coordinate) word)
            (ambientClosedDisk point, circle) := by
  fin_cases coordinate <;>
    simp [diskCellFourierParameterDerivative,
      closedMixedPlanarDerivativeCLM, fp17PlanarCoordinateCLM, spatialBasis]

private theorem diskCellFourierValue_differentiableAt
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ)
    (point : SpatialPlane) (membership : point ∈ openUnitDisk) :
    DifferentiableAt ℝ
      (closedDiskLift
        (diskCellFourierValue (closedMixedDerivative field order word) cell))
      point := by
  have parameterMeasurable : ∀ᶠ candidate in 𝓝 point,
      AEStronglyMeasurable
        (diskCellFourierParameter field word cell candidate)
          AddCircle.haarAddCircle := by
    filter_upwards [openUnitDisk_isOpen.mem_nhds membership] with candidate
      candidateMembership
    exact (diskCellFourierParameter_continuous_circle field word cell candidate
      candidateMembership).aestronglyMeasurable
  have parameterIntegrable : Integrable
      (diskCellFourierParameter field word cell point)
        AddCircle.haarAddCircle := by
    simpa only [integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        (diskCellFourierParameter_continuous_circle field word cell point
          membership).continuousOn)
  have derivativeMeasurable : AEStronglyMeasurable
      (diskCellFourierParameterDerivative field word cell point)
        AddCircle.haarAddCircle :=
    (diskCellFourierParameterDerivative_continuous_circle field word cell
      point).aestronglyMeasurable
  have derivativeBound : ∀ᵐ circle : CellCircle
      ∂AddCircle.haarAddCircle, ∀ candidate ∈ openUnitDisk,
      ‖diskCellFourierParameterDerivative field word cell candidate circle‖ ≤
        diskCellFourierDerivativeBound field word :=
    Filter.Eventually.of_forall fun circle candidate _ =>
      diskCellFourierParameterDerivative_norm_le field word cell candidate circle
  have boundIntegrable : Integrable
      (fun _ : CellCircle => diskCellFourierDerivativeBound field word)
        AddCircle.haarAddCircle := by
    simpa only [integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        (continuous_const : Continuous
          (fun _ : CellCircle =>
            diskCellFourierDerivativeBound field word)).continuousOn)
  have pointwiseDerivative : ∀ᵐ circle : CellCircle
      ∂AddCircle.haarAddCircle, ∀ candidate ∈ openUnitDisk,
      HasFDerivAt
        (fun source => diskCellFourierParameter field word cell source circle)
        (diskCellFourierParameterDerivative field word cell candidate circle)
        candidate :=
    Filter.Eventually.of_forall fun circle candidate candidateMembership =>
      diskCellFourierParameter_hasFDerivAt field word cell candidate
        candidateMembership circle
  have integralHas := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := AddCircle.haarAddCircle) (s := openUnitDisk)
    (F := fun candidate circle =>
      diskCellFourierParameter field word cell candidate circle)
    (F' := fun candidate circle =>
      diskCellFourierParameterDerivative field word cell candidate circle)
    (bound := fun _ : CellCircle =>
      diskCellFourierDerivativeBound field word)
    (openUnitDisk_isOpen.mem_nhds membership) parameterMeasurable
    parameterIntegrable derivativeMeasurable derivativeBound boundIntegrable
    pointwiseDerivative
  have localIntegralIdentity :
      closedDiskLift
          (diskCellFourierValue (closedMixedDerivative field order word) cell) =ᶠ[𝓝 point]
        (fun candidate => ∫ circle : CellCircle,
          diskCellFourierParameter field word cell candidate circle
            ∂AddCircle.haarAddCircle) := by
    filter_upwards [openUnitDisk_isOpen.mem_nhds membership] with candidate
      candidateMembership
    have closedMembership := openDiskMembershipClosed candidate
      candidateMembership
    rw [closedDiskLift, dif_pos closedMembership]
    rw [diskCellFourierValue_apply]
    unfold fourierCoeff diskCellFourierParameter
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun circle => by
      simp only [closedDiskLift, dif_pos closedMembership,
        diskCellSlice_apply]
  exact (integralHas.congr_of_eventuallyEq
    localIntegralIdentity).differentiableAt

/-- Planar differentiation commutes with the actual cell Fourier integral.
The proof uses the compact continuous derivative extensions as one uniform
dominating bound. -/
theorem diskCellFourierValue_fderiv_basis
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ)
    (point : SpatialPlane) (membership : point ∈ openUnitDisk)
    (coordinate : Fin 2) :
    fderiv ℝ
        (closedDiskLift
          (diskCellFourierValue (closedMixedDerivative field order word) cell))
        point (spatialBasis coordinate) =
      diskCellFourierValue
        (closedMixedDerivative field (order + 1)
          (Fin.cons (fp17PlanarCoordinate coordinate) word)) cell
        (ambientClosedDisk point) := by
  have parameterMeasurable : ∀ᶠ candidate in 𝓝 point,
      AEStronglyMeasurable
        (diskCellFourierParameter field word cell candidate)
          AddCircle.haarAddCircle := by
    filter_upwards [openUnitDisk_isOpen.mem_nhds membership] with candidate
      candidateMembership
    exact (diskCellFourierParameter_continuous_circle field word cell candidate
      candidateMembership).aestronglyMeasurable
  have parameterIntegrable : Integrable
      (diskCellFourierParameter field word cell point)
        AddCircle.haarAddCircle := by
    simpa only [integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        (diskCellFourierParameter_continuous_circle field word cell point
          membership).continuousOn)
  have derivativeMeasurable : AEStronglyMeasurable
      (diskCellFourierParameterDerivative field word cell point)
        AddCircle.haarAddCircle :=
    (diskCellFourierParameterDerivative_continuous_circle field word cell
      point).aestronglyMeasurable
  have derivativeBound : ∀ᵐ circle : CellCircle
      ∂AddCircle.haarAddCircle, ∀ candidate ∈ openUnitDisk,
      ‖diskCellFourierParameterDerivative field word cell candidate circle‖ ≤
        diskCellFourierDerivativeBound field word :=
    Filter.Eventually.of_forall fun circle candidate _ =>
      diskCellFourierParameterDerivative_norm_le field word cell candidate circle
  have boundIntegrable : Integrable
      (fun _ : CellCircle => diskCellFourierDerivativeBound field word)
        AddCircle.haarAddCircle := by
    simpa only [integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        (continuous_const : Continuous
          (fun _ : CellCircle =>
            diskCellFourierDerivativeBound field word)).continuousOn)
  have pointwiseDerivative : ∀ᵐ circle : CellCircle
      ∂AddCircle.haarAddCircle, ∀ candidate ∈ openUnitDisk,
      HasFDerivAt
        (fun source => diskCellFourierParameter field word cell source circle)
        (diskCellFourierParameterDerivative field word cell candidate circle)
        candidate :=
    Filter.Eventually.of_forall fun circle candidate candidateMembership =>
      diskCellFourierParameter_hasFDerivAt field word cell candidate
        candidateMembership circle
  have integralHas := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := AddCircle.haarAddCircle) (s := openUnitDisk)
    (F := fun candidate circle =>
      diskCellFourierParameter field word cell candidate circle)
    (F' := fun candidate circle =>
      diskCellFourierParameterDerivative field word cell candidate circle)
    (bound := fun _ : CellCircle =>
      diskCellFourierDerivativeBound field word)
    (openUnitDisk_isOpen.mem_nhds membership) parameterMeasurable
    parameterIntegrable derivativeMeasurable derivativeBound boundIntegrable
    pointwiseDerivative
  have localIntegralIdentity :
      closedDiskLift
          (diskCellFourierValue (closedMixedDerivative field order word) cell) =ᶠ[𝓝 point]
        (fun candidate => ∫ circle : CellCircle,
          diskCellFourierParameter field word cell candidate circle
            ∂AddCircle.haarAddCircle) := by
    filter_upwards [openUnitDisk_isOpen.mem_nhds membership] with candidate
      candidateMembership
    have closedMembership := openDiskMembershipClosed candidate
      candidateMembership
    rw [closedDiskLift, dif_pos closedMembership]
    rw [diskCellFourierValue_apply]
    unfold fourierCoeff diskCellFourierParameter
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun circle => by
      simp only [closedDiskLift, dif_pos closedMembership,
        diskCellSlice_apply]
  have coefficientHas : HasFDerivAt
      (closedDiskLift
        (diskCellFourierValue (closedMixedDerivative field order word) cell))
      (∫ circle : CellCircle,
        diskCellFourierParameterDerivative field word cell point circle
          ∂AddCircle.haarAddCircle) point :=
    integralHas.congr_of_eventuallyEq localIntegralIdentity
  have derivativeIntegrable : Integrable
      (diskCellFourierParameterDerivative field word cell point)
        AddCircle.haarAddCircle := by
    simpa only [integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        (diskCellFourierParameterDerivative_continuous_circle field word cell
          point).continuousOn)
  rw [coefficientHas.fderiv]
  calc
    (∫ circle : CellCircle,
        diskCellFourierParameterDerivative field word cell point circle
          ∂AddCircle.haarAddCircle) (spatialBasis coordinate) =
        ∫ circle : CellCircle,
          diskCellFourierParameterDerivative field word cell point circle
            (spatialBasis coordinate) ∂AddCircle.haarAddCircle := by
      simpa using
        (ContinuousLinearMap.integral_comp_comm
          (ContinuousLinearMap.apply ℝ (ComplexEuclidean dimension)
            (spatialBasis coordinate))
          derivativeIntegrable).symm
    _ = ∫ circle : CellCircle,
        fourier (-cell) circle •
          closedMixedDerivative field (order + 1)
            (Fin.cons (fp17PlanarCoordinate coordinate) word)
              (ambientClosedDisk point, circle)
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun circle =>
        diskCellFourierParameterDerivative_basis field word cell point circle
          coordinate
    _ = diskCellFourierValue
        (closedMixedDerivative field (order + 1)
          (Fin.cons (fp17PlanarCoordinate coordinate) word)) cell
        (ambientClosedDisk point) := by
      rw [diskCellFourierValue_apply]
      rfl

private def diskCellFourierCoefficientFunction
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ) :
    SpatialPlane → ComplexEuclidean dimension :=
  closedDiskLift
    (diskCellFourierValue (closedMixedDerivative field order word) cell)

private def diskCellFourierSuccessorCLM
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ) (point : SpatialPlane) :
    SpatialPlane →L[ℝ] ComplexEuclidean dimension :=
  (ContinuousLinearMap.smulRightL ℝ SpatialPlane
      (ComplexEuclidean dimension)) (fp17PlanarCoordinateCLM 0)
        (diskCellFourierCoefficientFunction field
          (Fin.cons (fp17PlanarCoordinate 0) word) cell point) +
    (ContinuousLinearMap.smulRightL ℝ SpatialPlane
      (ComplexEuclidean dimension)) (fp17PlanarCoordinateCLM 1)
        (diskCellFourierCoefficientFunction field
          (Fin.cons (fp17PlanarCoordinate 1) word) cell point)

private theorem diskCellFourierCoefficientFunction_fderiv_basis
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ)
    (point : SpatialPlane) (membership : point ∈ openUnitDisk)
    (coordinate : Fin 2) :
    fderiv ℝ (diskCellFourierCoefficientFunction field word cell) point
        (spatialBasis coordinate) =
      diskCellFourierSuccessorCLM field word cell point
        (spatialBasis coordinate) := by
  rw [diskCellFourierCoefficientFunction,
    diskCellFourierValue_fderiv_basis field word cell point membership coordinate]
  have closedMembership := openDiskMembershipClosed point membership
  have ambientIdentity : ambientClosedDisk point =
      (⟨point, closedMembership⟩ : ClosedDisk) := by
    apply Subtype.ext
    exact ambientClosedDisk_val_of_mem closedMembership
  fin_cases coordinate <;>
    simp [diskCellFourierSuccessorCLM,
      diskCellFourierCoefficientFunction, fp17PlanarCoordinateCLM,
      spatialBasis, closedDiskLift, closedMembership, ambientIdentity]

private theorem diskCellFourierCoefficientFunction_fderiv_prepend
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ)
    (point : SpatialPlane) (membership : point ∈ openUnitDisk)
    (coordinate : Fin 2) :
    fderiv ℝ (diskCellFourierCoefficientFunction field word cell) point
        (spatialBasis coordinate) =
      diskCellFourierCoefficientFunction field
        (Fin.cons (fp17PlanarCoordinate coordinate) word) cell point := by
  rw [diskCellFourierCoefficientFunction_fderiv_basis field word cell point
    membership coordinate]
  fin_cases coordinate <;>
    simp [diskCellFourierSuccessorCLM, fp17PlanarCoordinateCLM, spatialBasis]

private theorem diskCellFourierCoefficientFunction_fderiv_eq
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ)
    (point : SpatialPlane) (membership : point ∈ openUnitDisk) :
    fderiv ℝ (diskCellFourierCoefficientFunction field word cell) point =
      diskCellFourierSuccessorCLM field word cell point := by
  apply ContinuousLinearMap.ext
  intro direction
  have planeExpansion :
      (∑ coordinate : Fin 2,
        (direction coordinate) • spatialBasis coordinate) = direction := by
    ext component
    fin_cases component <;> simp [Fin.sum_univ_two, spatialBasis]
  calc
    fderiv ℝ (diskCellFourierCoefficientFunction field word cell) point
        direction =
        fderiv ℝ (diskCellFourierCoefficientFunction field word cell) point
          (∑ coordinate : Fin 2,
            (direction coordinate) • spatialBasis coordinate) := by
      rw [planeExpansion]
    _ = ∑ coordinate : Fin 2, (direction coordinate) •
        fderiv ℝ (diskCellFourierCoefficientFunction field word cell) point
          (spatialBasis coordinate) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [map_smul]
    _ = ∑ coordinate : Fin 2, (direction coordinate) •
        diskCellFourierSuccessorCLM field word cell point
          (spatialBasis coordinate) := by
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [diskCellFourierCoefficientFunction_fderiv_basis field word cell point
        membership coordinate]
    _ = diskCellFourierSuccessorCLM field word cell point direction := by
      symm
      calc
        _ = diskCellFourierSuccessorCLM field word cell point
            (∑ coordinate : Fin 2,
              (direction coordinate) • spatialBasis coordinate) := by
          rw [planeExpansion]
        _ = _ := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro coordinate _
          rw [map_smul]

private theorem diskCellFourierCoefficientFunction_contDiffOn_nat
    (smoothness : ℕ) {dimension order : ℕ}
    (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ) :
    ContDiffOn ℝ smoothness
      (diskCellFourierCoefficientFunction field word cell) openUnitDisk := by
  induction smoothness generalizing order with
  | zero =>
      change ContDiffOn ℝ (0 : WithTop ℕ∞)
        (diskCellFourierCoefficientFunction field word cell) openUnitDisk
      rw [contDiffOn_zero]
      intro point membership
      exact (diskCellFourierValue_differentiableAt field word cell point
        membership).continuousAt.continuousWithinAt
  | succ smoothness inductionHypothesis =>
      rw [show (smoothness.succ : WithTop ℕ∞) =
          (smoothness : WithTop ℕ∞) + 1 by norm_num]
      apply (contDiffOn_succ_iff_fderiv_of_isOpen openUnitDisk_isOpen).2
      refine ⟨?_, ?_, ?_⟩
      · intro point membership
        exact (diskCellFourierValue_differentiableAt field word cell point
          membership).differentiableWithinAt
      · intro impossible
        norm_num at impossible
      · have zeroSmooth := inductionHypothesis (order := order + 1)
          (Fin.cons (fp17PlanarCoordinate 0) word)
        have oneSmooth := inductionHypothesis (order := order + 1)
          (Fin.cons (fp17PlanarCoordinate 1) word)
        have zeroCLMSmooth : ContDiffOn ℝ smoothness
            (fun point =>
              (ContinuousLinearMap.smulRightL ℝ SpatialPlane
                (ComplexEuclidean dimension)) (fp17PlanarCoordinateCLM 0)
                  (diskCellFourierCoefficientFunction field
                    (Fin.cons (fp17PlanarCoordinate 0) word) cell point))
            openUnitDisk :=
          ((ContinuousLinearMap.smulRightL ℝ SpatialPlane
            (ComplexEuclidean dimension))
              (fp17PlanarCoordinateCLM 0)).contDiff.fun_comp_contDiffOn
                zeroSmooth
        have oneCLMSmooth : ContDiffOn ℝ smoothness
            (fun point =>
              (ContinuousLinearMap.smulRightL ℝ SpatialPlane
                (ComplexEuclidean dimension)) (fp17PlanarCoordinateCLM 1)
                  (diskCellFourierCoefficientFunction field
                    (Fin.cons (fp17PlanarCoordinate 1) word) cell point))
            openUnitDisk :=
          ((ContinuousLinearMap.smulRightL ℝ SpatialPlane
            (ComplexEuclidean dimension))
              (fp17PlanarCoordinateCLM 1)).contDiff.fun_comp_contDiffOn
                oneSmooth
        have successorSmooth : ContDiffOn ℝ smoothness
            (diskCellFourierSuccessorCLM field word cell) openUnitDisk :=
          zeroCLMSmooth.add oneCLMSmooth
        exact successorSmooth.congr (fun point membership =>
          diskCellFourierCoefficientFunction_fderiv_eq field word cell point
            membership)

private theorem diskCellFourierCoefficientFunction_contDiffOn
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ) :
    ContDiffOn ℝ ∞ (diskCellFourierCoefficientFunction field word cell)
      openUnitDisk := by
  apply contDiffOn_infty.mpr
  intro smoothness
  exact diskCellFourierCoefficientFunction_contDiffOn_nat smoothness field word
    cell

/-- The basic Fourier coefficient value is smooth on the open disk. -/
theorem diskCellFourierValue_contDiffOn
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (cell : ℤ) :
    ContDiffOn ℝ ∞
      (closedDiskLift (diskCellFourierValue field.value cell)) openUnitDisk := by
  simpa [diskCellFourierCoefficientFunction,
    closedMixedDerivative_zero_order] using
    (diskCellFourierCoefficientFunction_contDiffOn field
      emptyMixedCartesianWord cell)

/-- Exact ordered planar derivative formula for the Fourier coefficient of
an arbitrary ordinary disk-cell closed jet. -/
theorem cartesianDerivative_diskCellFourierValue
    {dimension order : ℕ} (field : DiskCellClosedJet dimension) (cell : ℤ)
    (word : CartesianWord order) (point : SpatialPlane)
    (membership : point ∈ openUnitDisk) :
    cartesianDerivative order word
        (closedDiskLift (diskCellFourierValue field.value cell)) point =
      diskCellFourierCoefficientFunction field (fp17LiftPlanarWord word) cell
        point := by
  induction order generalizing point with
  | zero =>
      have wordIdentity : word = emptyCartesianWord := Subsingleton.elim _ _
      subst word
      change closedDiskLift (diskCellFourierValue field.value cell) point =
        closedDiskLift
          (diskCellFourierValue
            (closedMixedDerivative field 0 (fp17LiftPlanarWord emptyCartesianWord))
            cell) point
      rw [show fp17LiftPlanarWord emptyCartesianWord =
          emptyMixedCartesianWord from Subsingleton.elim _ _,
        closedMixedDerivative_zero_order]
  | succ order inductionHypothesis =>
      have baseSmooth := diskCellFourierValue_contDiffOn field cell
      have baseSmoothAt := baseSmooth.contDiffAt
        (openUnitDisk_isOpen.mem_nhds membership)
      have derivativeDifferentiable :=
        baseSmoothAt.differentiableAt_iteratedFDeriv
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl order)
      have successor := derivativeDifferentiable.iteratedFDeriv_succ_apply_left'
        (m := fun position => spatialBasis (word position))
      have localInduction :
          (fun candidate => cartesianDerivative order (Fin.tail word)
            (closedDiskLift (diskCellFourierValue field.value cell)) candidate) =ᶠ[𝓝 point]
          diskCellFourierCoefficientFunction field
            (fp17LiftPlanarWord (Fin.tail word)) cell :=
        Filter.eventually_of_mem (openUnitDisk_isOpen.mem_nhds membership)
          (fun candidate candidateMembership =>
            inductionHypothesis (Fin.tail word) candidate candidateMembership)
      change (iteratedFDeriv ℝ (order + 1)
          (closedDiskLift (diskCellFourierValue field.value cell)) point)
          (fun position => spatialBasis (word position)) = _
      rw [successor]
      change fderiv ℝ
          (fun candidate => cartesianDerivative order (Fin.tail word)
            (closedDiskLift (diskCellFourierValue field.value cell)) candidate)
          point (spatialBasis (word 0)) = _
      rw [localInduction.fderiv_eq]
      rw [diskCellFourierCoefficientFunction_fderiv_prepend field
        (fp17LiftPlanarWord (Fin.tail word)) cell point membership (word 0)]
      congr 2
      funext position
      exact Fin.cases rfl (fun _ => rfl) position

/-- The continuous extension of a requested planar Fourier-coefficient
derivative. -/
def diskCellFourierDerivativeExtension
    {dimension order : ℕ} (field : DiskCellClosedJet dimension) (cell : ℤ)
    (word : CartesianWord order) :
    C(ClosedDisk, ComplexEuclidean dimension) :=
  diskCellFourierValue
    (closedMixedDerivative field order (fp17LiftPlanarWord word)) cell

theorem diskCellFourierDerivativeExtension_spec
    {dimension order : ℕ} (field : DiskCellClosedJet dimension) (cell : ℤ)
    (word : CartesianWord order) :
    IsCartesianExtension (diskCellFourierValue field.value cell) order word
      (diskCellFourierDerivativeExtension field cell word) := by
  intro point membership
  rw [diskCellFourierDerivativeExtension]
  rw [cartesianDerivative_diskCellFourierValue field cell word point.val
    membership]
  unfold diskCellFourierCoefficientFunction
  rw [closedDiskLift, dif_pos (openDiskMembershipClosed point.val membership)]

/-- The exact cell Fourier coefficient as an actual closed jet on the disk. -/
def diskCellFourierCoefficientJet
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (cell : ℤ) :
    ClosedJet dimension where
  value := diskCellFourierValue field.value cell
  smoothInterior := diskCellFourierValue_contDiffOn field cell
  derivativeExists := fun _order word =>
    ⟨diskCellFourierDerivativeExtension field cell word,
      diskCellFourierDerivativeExtension_spec field cell word⟩

@[simp] theorem diskCellFourierCoefficientJet_value
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (cell : ℤ) :
    (diskCellFourierCoefficientJet field cell).value =
      diskCellFourierValue field.value cell := rfl

end Grad.CartesianState
