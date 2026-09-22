import P0910Periodization
import Mathlib.Analysis.Calculus.FDeriv.WithLp

noncomputable section

open Filter Set
open scoped BigOperators ContDiff Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets
open Grad.DiskExtension.Seeley

local instance p0910ExteriorClosedDiskCompactSpace : CompactSpace ClosedDisk := by
  rw [← isCompact_iff_compactSpace, closedUnitDisk_eq_closedBall]
  exact isCompact_closedBall (0 : SpatialPlane) 1

def normalizedSpatialCell (point : SpatialCell) : SpatialCell :=
  assembleSpatialCell (‖planarPart point‖⁻¹ • planarPart point) (point 2)

theorem normalizedSpatialCell_contDiffAt (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    ContDiffAt ℝ ∞ normalizedSpatialCell point := by
  have normSmooth := contDiffAt_norm_planarPart point nonzero
  have planarSmooth : ContDiff ℝ ∞ planarPart := by
    change ContDiff ℝ ∞ (fun candidate : SpatialCell => planarPartCLM candidate)
    exact planarPartCLM.contDiff
  have normNonzero : ‖planarPart point‖ ≠ 0 := norm_ne_zero_iff.mpr nonzero
  have normalized : ContDiffAt ℝ ∞
      (fun candidate : SpatialCell =>
        ‖planarPart candidate‖⁻¹ • planarPart candidate) point :=
    (normSmooth.inv normNonzero).smul planarSmooth.contDiffAt
  have cellSmooth : ContDiffAt ℝ ∞
      (fun candidate : SpatialCell => candidate 2) point := by
    change ContDiffAt ℝ ∞ (fun candidate : SpatialCell => cellCoordinateCLM candidate) point
    exact cellCoordinateCLM.contDiff.contDiffAt
  rw [show normalizedSpatialCell = fun candidate =>
      assembleSpatialCellCLM
        (‖planarPart candidate‖⁻¹ • planarPart candidate, candidate 2) by
    funext candidate
    simp [normalizedSpatialCell]]
  exact assembleSpatialCellCLM.contDiff.contDiffAt.comp point
    (normalized.prodMk cellSmooth)

theorem radialNormCell_fderiv_norm_le (point : SpatialCell) :
    ‖fderiv ℝ (fun candidate : SpatialCell => ‖planarPart candidate‖) point‖ ≤
      ‖planarPartCLM‖ := by
  change ‖fderiv ℝ (norm ∘ (planarPartCLM : SpatialCell → SpatialPlane)) point‖ ≤
    (‖planarPartCLM‖₊ : ℝ)
  simpa only [one_mul] using
    (norm_fderiv_le_of_lipschitz ℝ
      (x₀ := point) (lipschitzWith_one_norm.comp planarPartCLM.lipschitz))

noncomputable def plateauFirstBound : ℝ :=
  Classical.choose (plateauCutoff_iteratedDeriv_bound 1)

theorem plateauFirstBound_nonnegative : 0 ≤ plateauFirstBound :=
  (Classical.choose_spec (plateauCutoff_iteratedDeriv_bound 1)).1

theorem plateauCutoff_deriv_norm_le (scale : ℝ) :
    ‖deriv plateauCutoff scale‖ ≤ plateauFirstBound := by
  rw [← iteratedDeriv_one]
  exact (Classical.choose_spec (plateauCutoff_iteratedDeriv_bound 1)).2 scale

noncomputable def plateauFirstNNBound : NNReal :=
  ⟨plateauFirstBound, plateauFirstBound_nonnegative⟩

theorem plateauCutoff_lipschitz :
    LipschitzWith plateauFirstNNBound plateauCutoff := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (plateauCutoff_smooth.differentiable (by simp))
  intro scale
  apply NNReal.coe_le_coe.mp
  change ‖deriv plateauCutoff scale‖ ≤ plateauFirstBound
  exact plateauCutoff_deriv_norm_le scale

theorem reflectedSpatialCell_affine (index : ℕ) (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    reflectedSpatialCell index point =
      (1 + node index) • normalizedSpatialCell point - node index • point := by
  have normNonzero : ‖planarPart point‖ ≠ 0 := norm_ne_zero_iff.mpr nonzero
  ext coordinate
  fin_cases coordinate
  · change (1 - node index * (‖planarPart point‖ - 1)) *
        (‖planarPart point‖⁻¹ * point 0) =
      (1 + node index) * (‖planarPart point‖⁻¹ * point 0) - node index * point 0
    field_simp
    ring
  · change (1 - node index * (‖planarPart point‖ - 1)) *
        (‖planarPart point‖⁻¹ * point 1) =
      (1 + node index) * (‖planarPart point‖⁻¹ * point 1) - node index * point 1
    field_simp
    ring
  · change point 2 = (1 + node index) * point 2 - node index * point 2
    ring

theorem reflectedSpatialCell_fderiv (index : ℕ) (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    fderiv ℝ (reflectedSpatialCell index) point =
      (1 + node index) • fderiv ℝ normalizedSpatialCell point -
        node index • ContinuousLinearMap.id ℝ SpatialCell := by
  have rightDerivative : HasFDerivAt
      ((1 + node index) • normalizedSpatialCell - node index • id)
      ((1 + node index) • fderiv ℝ normalizedSpatialCell point -
        node index • ContinuousLinearMap.id ℝ SpatialCell) point :=
    (((normalizedSpatialCell_contDiffAt point nonzero).differentiableAt
      (by simp)).hasFDerivAt.const_smul (1 + node index)).sub
        ((hasFDerivAt_id point).const_smul (node index))
  have nonzeroNeighborhood : ∀ᶠ candidate in 𝓝 point, planarPart candidate ≠ 0 := by
    exact continuous_planarPart.continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds nonzero)
  apply (rightDerivative.congr_of_eventuallyEq ?_).fderiv
  filter_upwards [nonzeroNeighborhood] with candidate candidateNonzero
  exact reflectedSpatialCell_affine index candidate candidateNonzero

def exteriorScalar (index : ℕ) (point : SpatialCell) : ℂ :=
  ((coefficient index *
    plateauCutoff (node index * (‖planarPart point‖ - 1)) : ℝ) : ℂ)

theorem exteriorScalar_contDiffAt (index : ℕ) (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    ContDiffAt ℝ ∞ (exteriorScalar index) point := by
  have normSmooth := contDiffAt_norm_planarPart point nonzero
  have scaleSmooth : ContDiffAt ℝ ∞
      (fun candidate : SpatialCell =>
        node index * (‖planarPart candidate‖ - 1)) point :=
    contDiffAt_const.mul (normSmooth.sub contDiffAt_const)
  have cutoffSmooth : ContDiffAt ℝ ∞
      (fun candidate : SpatialCell =>
        plateauCutoff (node index * (‖planarPart candidate‖ - 1))) point :=
    plateauCutoff_smooth.contDiffAt.comp point scaleSmooth
  have realScalarSmooth : ContDiffAt ℝ ∞
      (fun candidate : SpatialCell => coefficient index *
        plateauCutoff (node index * (‖planarPart candidate‖ - 1))) point :=
    contDiffAt_const.mul cutoffSmooth
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp point realScalarSmooth

theorem exteriorScalar_fderiv_norm_le (index : ℕ) (point : SpatialCell) :
    ‖fderiv ℝ (exteriorScalar index) point‖ ≤
      |coefficient index| * plateauFirstBound * node index * ‖planarPartCLM‖ := by
  apply norm_fderiv_le_of_lip' ℝ
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg _) plateauFirstBound_nonnegative)
        (node_positive index).le)
      (norm_nonneg _)
  · apply Filter.Eventually.of_forall
    intro candidate
    let candidateScale := node index * (‖planarPart candidate‖ - 1)
    let pointScale := node index * (‖planarPart point‖ - 1)
    have cutoffDifference :=
      plateauCutoff_lipschitz.norm_sub_le candidateScale pointScale
    change |plateauCutoff candidateScale - plateauCutoff pointScale| ≤
      plateauFirstBound * |candidateScale - pointScale| at cutoffDifference
    have normDifference := abs_norm_sub_norm_le
      (planarPart candidate) (planarPart point)
    have planarDifference :
        ‖planarPart candidate - planarPart point‖ ≤
          ‖planarPartCLM‖ * ‖candidate - point‖ := by
      change ‖planarPartCLM candidate - planarPartCLM point‖ ≤
        ‖planarPartCLM‖ * ‖candidate - point‖
      rw [← planarPartCLM.map_sub]
      exact ContinuousLinearMap.le_opNorm _ _
    have scaleDifference : |candidateScale - pointScale| ≤
        node index * ‖planarPartCLM‖ * ‖candidate - point‖ := by
      rw [show candidateScale - pointScale =
        node index * (‖planarPart candidate‖ - ‖planarPart point‖) by
          dsimp only [candidateScale, pointScale]
          ring,
        abs_mul, abs_of_pos (node_positive index)]
      calc
        node index * |‖planarPart candidate‖ - ‖planarPart point‖| ≤
            node index * ‖planarPart candidate - planarPart point‖ := by
          exact mul_le_mul_of_nonneg_left normDifference (node_positive index).le
        _ ≤ node index * (‖planarPartCLM‖ * ‖candidate - point‖) := by
          exact mul_le_mul_of_nonneg_left planarDifference (node_positive index).le
        _ = node index * ‖planarPartCLM‖ * ‖candidate - point‖ := by ring
    calc
      ‖exteriorScalar index candidate - exteriorScalar index point‖ =
          |coefficient index| *
            |plateauCutoff candidateScale - plateauCutoff pointScale| := by
        simp only [exteriorScalar, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, ← mul_sub, candidateScale, pointScale, abs_mul]
      _ ≤ |coefficient index| *
          (plateauFirstBound * |candidateScale - pointScale|) := by
        exact mul_le_mul_of_nonneg_left cutoffDifference (abs_nonneg _)
      _ ≤ |coefficient index| *
          (plateauFirstBound *
            (node index * ‖planarPartCLM‖ * ‖candidate - point‖)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left scaleDifference plateauFirstBound_nonnegative)
          (abs_nonneg _)
      _ = (|coefficient index| * plateauFirstBound * node index *
          ‖planarPartCLM‖) * ‖candidate - point‖ := by ring

theorem exteriorScalar_norm_le (index : ℕ) (point : SpatialCell) :
    ‖exteriorScalar index point‖ ≤ |coefficient index| := by
  rw [exteriorScalar, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (plateauCutoff_range _).1]
  exact mul_le_of_le_one_right (abs_nonneg _) (plateauCutoff_range _).2

theorem eventually_reflectedSpatialCell_fderiv_norm_le_boundary
    (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    ∀ᶠ candidate in 𝓝 point, ∀ index,
      ‖fderiv ℝ (reflectedSpatialCell index) candidate‖ ≤
        (2 * (‖fderiv ℝ normalizedSpatialCell point‖ + 1) + 1) * node index := by
  have planarNonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at boundary
    norm_num at boundary
  have derivativeContinuous :=
    (normalizedSpatialCell_contDiffAt point planarNonzero).continuousAt_fderiv (by simp)
  have derivativeBound : ∀ᶠ candidate in 𝓝 point,
      ‖fderiv ℝ normalizedSpatialCell candidate‖ <
        ‖fderiv ℝ normalizedSpatialCell point‖ + 1 :=
    derivativeContinuous.norm.eventually
      (Iio_mem_nhds (lt_add_one ‖fderiv ℝ normalizedSpatialCell point‖))
  have nonzeroNeighborhood : ∀ᶠ candidate in 𝓝 point,
      planarPart candidate ≠ 0 :=
    continuous_planarPart.continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds planarNonzero)
  filter_upwards [derivativeBound, nonzeroNeighborhood] with candidate candidateBound
    candidateNonzero index
  rw [reflectedSpatialCell_fderiv index candidate candidateNonzero]
  calc
    ‖(1 + node index) • fderiv ℝ normalizedSpatialCell candidate -
        node index • ContinuousLinearMap.id ℝ SpatialCell‖ ≤
        ‖(1 + node index) • fderiv ℝ normalizedSpatialCell candidate‖ +
          ‖node index • ContinuousLinearMap.id ℝ SpatialCell‖ := norm_sub_le _ _
    _ = (1 + node index) * ‖fderiv ℝ normalizedSpatialCell candidate‖ +
        node index := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by linarith [node_positive index]),
        abs_of_pos (node_positive index), ContinuousLinearMap.norm_id]
      ring
    _ ≤ (1 + node index) *
          (‖fderiv ℝ normalizedSpatialCell point‖ + 1) + node index := by
      have coefficientNonnegative : 0 ≤ 1 + node index := by
        linarith [node_positive index]
      simpa only [add_comm] using add_le_add_right
        (mul_le_mul_of_nonneg_left candidateBound.le coefficientNonnegative)
        (node index)
    _ ≤ (2 * (‖fderiv ℝ normalizedSpatialCell point‖ + 1) + 1) *
          node index := by
      have nodeBound := node_one_le index
      have derivativeNonnegative : 0 ≤ ‖fderiv ℝ normalizedSpatialCell point‖ + 1 := by
        positivity
      nlinarith

theorem exteriorScalar_eventually_boundary (index : ℕ) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    exteriorScalar index =ᶠ[𝓝 point] fun _ => (coefficient index : ℂ) := by
  have planarNonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at boundary
    norm_num at boundary
  have scaleContinuous : ContinuousAt
      (fun candidate : SpatialCell => node index * (‖planarPart candidate‖ - 1)) point :=
    ((contDiffAt_norm_planarPart point planarNonzero).continuousAt.sub
      continuousAt_const).const_mul _
  have scaleAt : node index * (‖planarPart point‖ - 1) < cutoffPlateauWidth := by
    rw [boundary, sub_self, mul_zero, collar_constants.2.1]
    norm_num
  filter_upwards [scaleContinuous.eventually (Iio_mem_nhds scaleAt)] with candidate bound
  rw [exteriorScalar, plateauCutoff_one _ bound.le]
  simp

theorem exteriorScalar_fderiv_boundary (index : ℕ) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    fderiv ℝ (exteriorScalar index) point = 0 := by
  have constantDerivative : HasFDerivAt
      (fun _ : SpatialCell => (coefficient index : ℂ))
      (0 : SpatialCell →L[ℝ] ℂ) point := hasFDerivAt_const _ _
  exact (constantDerivative.congr_of_eventuallyEq
    (exteriorScalar_eventually_boundary index point boundary)).fderiv

theorem exteriorScalar_iteratedFDeriv_boundary (index : ℕ) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) (order : ℕ) (positive : 0 < order) :
    iteratedFDeriv ℝ order (exteriorScalar index) point = 0 := by
  have derivatives := (exteriorScalar_eventually_boundary index point boundary).iteratedFDeriv
    ℝ order
  rw [iteratedFDeriv_const_of_ne (Nat.ne_of_gt positive) (coefficient index : ℂ)]
    at derivatives
  exact derivatives.eq_of_nhds

noncomputable def closedFirstDerivativeDiskMap {dimension : ℕ}
    (field : DiskCellClosedJet dimension) :
    C(DiskCellDomain, SpatialCell →L[ℝ] ComplexEuclidean dimension) where
  toFun diskPoint := ∑ coordinate : Fin 3,
    (spatialCellCoordinateCLM coordinate).smulRight
      (closedMixedDerivative field 1 (fun _ => coordinate) diskPoint)
  continuous_toFun := by
    apply continuous_finsetSum
    intro coordinate _
    exact ((ContinuousLinearMap.smulRightL ℝ SpatialCell
      (ComplexEuclidean dimension))
        (spatialCellCoordinateCLM coordinate)).continuous.comp
          (closedMixedDerivative field 1 (fun _ => coordinate)).continuous

theorem closedFirstDerivative_norm_le {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell) :
    ‖closedFirstDerivative field point‖ ≤ ‖closedFirstDerivativeDiskMap field‖ := by
  change ‖closedFirstDerivativeDiskMap field (retractedDiskCell point)‖ ≤
    ‖closedFirstDerivativeDiskMap field‖
  exact (closedFirstDerivativeDiskMap field).norm_coe_le_norm _

noncomputable def exteriorFirstModelBoundConstant {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell) : ℝ :=
  ‖closedFirstDerivativeDiskMap field‖ *
      (2 * (‖fderiv ℝ normalizedSpatialCell point‖ + 1) + 1) +
    plateauFirstBound * ‖planarPartCLM‖ * ‖field.value‖

theorem exteriorFirstModelBoundConstant_nonnegative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell) :
    0 ≤ exteriorFirstModelBoundConstant field point := by
  unfold exteriorFirstModelBoundConstant
  exact add_nonneg
    (mul_nonneg (norm_nonneg (closedFirstDerivativeDiskMap field))
      (by positivity : 0 ≤ 2 * (‖fderiv ℝ normalizedSpatialCell point‖ + 1) + 1))
    (mul_nonneg
      (mul_nonneg plateauFirstBound_nonnegative (norm_nonneg _))
      (norm_nonneg _))

theorem exteriorFirstModel_majorant_summable {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell) :
    Summable (fun index => exteriorFirstModelBoundConstant field point *
      (|coefficient index| * node index)) := by
  simpa only [pow_one] using
    (coefficient_absolute_moment_summable 1).mul_left
      (exteriorFirstModelBoundConstant field point)

theorem coefficient_node_summable :
    Summable (fun index => coefficient index * node index) := by
  simpa only [pow_one, mul_neg, neg_neg] using
    (coefficient_signed_moment_summable 1).neg

theorem coefficient_node_tsum :
    ∑' index, coefficient index * node index = -1 := by
  calc
    ∑' index, coefficient index * node index =
        ∑' index, -(coefficient index * (-node index) ^ (1 : ℕ)) := by
          congr 1
          funext index
          simp
    _ = -(∑' index, coefficient index * (-node index) ^ (1 : ℕ)) := by
      rw [tsum_neg]
    _ = -1 := by rw [infinite_moment_tsum]

theorem coefficient_reflectedSpatialCell_fderiv_tsum (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    ∑' index, coefficient index • fderiv ℝ (reflectedSpatialCell index) point =
      ContinuousLinearMap.id ℝ SpatialCell := by
  let normalizedDerivative := fderiv ℝ normalizedSpatialCell point
  have scalarSummable : Summable
      (fun index => coefficient index * (1 + node index)) := by
    convert coefficient_summable.add coefficient_node_summable using 1
    funext index
    ring
  have summableNormalized : Summable (fun index =>
      (coefficient index * (1 + node index)) • normalizedDerivative) :=
    scalarSummable.smul_const _
  have summableIdentity : Summable (fun index =>
      (coefficient index * node index) • ContinuousLinearMap.id ℝ SpatialCell) :=
    coefficient_node_summable.smul_const _
  have termEquality : (fun index => coefficient index •
      fderiv ℝ (reflectedSpatialCell index) point) = fun index =>
        (coefficient index * (1 + node index)) • normalizedDerivative -
          (coefficient index * node index) •
            ContinuousLinearMap.id ℝ SpatialCell := by
    funext index
    rw [reflectedSpatialCell_fderiv index point nonzero]
    dsimp only [normalizedDerivative]
    module
  rw [termEquality]
  rw [summableNormalized.tsum_sub summableIdentity]
  have scalarTsum : ∑' index, coefficient index * (1 + node index) = 0 := by
    rw [show (fun index => coefficient index * (1 + node index)) =
      (fun index => coefficient index) + fun index => coefficient index * node index by
        funext index
        simp
        ring]
    calc
      tsum ((fun index => coefficient index) +
          fun index => coefficient index * node index) =
          tsum coefficient + tsum (fun index => coefficient index * node index) :=
        coefficient_summable.tsum_add coefficient_node_summable
      _ = 0 := by rw [coefficient_tsum, coefficient_node_tsum]; ring
  have normalizedTsum := scalarSummable.tsum_smul_const normalizedDerivative
  rw [scalarTsum, zero_smul] at normalizedTsum
  rw [normalizedTsum]
  rw [coefficient_node_summable.tsum_smul_const, coefficient_node_tsum]
  module

theorem coefficient_reflectedSpatialCell_fderiv_summable (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    Summable (fun index =>
      coefficient index • fderiv ℝ (reflectedSpatialCell index) point) := by
  let normalizedDerivative := fderiv ℝ normalizedSpatialCell point
  have scalarSummable : Summable
      (fun index => coefficient index * (1 + node index)) := by
    convert coefficient_summable.add coefficient_node_summable using 1
    funext index
    ring
  have summableNormalized : Summable (fun index =>
      (coefficient index * (1 + node index)) • normalizedDerivative) :=
    scalarSummable.smul_const _
  have summableIdentity : Summable (fun index =>
      (coefficient index * node index) • ContinuousLinearMap.id ℝ SpatialCell) :=
    coefficient_node_summable.smul_const _
  have termEquality : (fun index => coefficient index •
      fderiv ℝ (reflectedSpatialCell index) point) = fun index =>
        (coefficient index * (1 + node index)) • normalizedDerivative -
          (coefficient index * node index) •
            ContinuousLinearMap.id ℝ SpatialCell := by
    funext index
    rw [reflectedSpatialCell_fderiv index point nonzero]
    dsimp only [normalizedDerivative]
    module
  rw [termEquality]
  exact summableNormalized.sub summableIdentity

theorem coefficient_closedFirstDerivative_reflection_tsum {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    ∑' index, coefficient index •
        (closedFirstDerivative field point).comp
          (fderiv ℝ (reflectedSpatialCell index) point) =
      closedFirstDerivative field point := by
  let composeMap :
      (SpatialCell →L[ℝ] SpatialCell) →L[ℝ]
        (SpatialCell →L[ℝ] ComplexEuclidean dimension) :=
    (ContinuousLinearMap.compL ℝ SpatialCell SpatialCell
      (ComplexEuclidean dimension)) (closedFirstDerivative field point)
  have summable :=
    coefficient_reflectedSpatialCell_fderiv_summable point nonzero
  have termEquality : (fun index => coefficient index •
      (closedFirstDerivative field point).comp
        (fderiv ℝ (reflectedSpatialCell index) point)) = fun index =>
      composeMap (coefficient index •
        fderiv ℝ (reflectedSpatialCell index) point) := by
    funext index
    simp [composeMap, ContinuousLinearMap.compL_apply]
  rw [termEquality, ← composeMap.map_tsum summable,
    coefficient_reflectedSpatialCell_fderiv_tsum point nonzero]
  simp [composeMap, ContinuousLinearMap.compL_apply]

noncomputable def exteriorSummandFirstModel {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : ℕ) (point : SpatialCell) :
    SpatialCell →L[ℝ] ComplexEuclidean dimension :=
    exteriorScalar index point •
      (closedFirstDerivative field (reflectedSpatialCell index point)).comp
        (fderiv ℝ (reflectedSpatialCell index) point) +
    (fderiv ℝ (exteriorScalar index) point).smulRight
      (field.value (retractedDiskCell (reflectedSpatialCell index point)))

theorem norm_complex_smulRight_le {dimension : ℕ}
    (functional : SpatialCell →L[ℝ] ℂ)
    (value : ComplexEuclidean dimension) :
    ‖functional.smulRight value‖ ≤ ‖functional‖ * ‖value‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro direction
  rw [ContinuousLinearMap.smulRight_apply, norm_smul]
  calc
    ‖functional direction‖ * ‖value‖ ≤
        (‖functional‖ * ‖direction‖) * ‖value‖ := by
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.le_opNorm functional direction) (norm_nonneg _)
    _ = (‖functional‖ * ‖value‖) * ‖direction‖ := by ring

theorem eventually_exteriorSummandFirstModel_norm_le_boundary {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    ∀ᶠ candidate in 𝓝 point, ∀ index,
      ‖exteriorSummandFirstModel field index candidate‖ ≤
        exteriorFirstModelBoundConstant field point *
          (|coefficient index| * node index) := by
  filter_upwards [eventually_reflectedSpatialCell_fderiv_norm_le_boundary
    point boundary] with candidate reflectionBound index
  have closedBound := closedFirstDerivative_norm_le field
    (reflectedSpatialCell index candidate)
  have scalarBound := exteriorScalar_norm_le index candidate
  have scalarDerivativeBound := exteriorScalar_fderiv_norm_le index candidate
  have sampleBound :
      ‖field.value (retractedDiskCell (reflectedSpatialCell index candidate))‖ ≤
        ‖field.value‖ :=
    field.value.norm_coe_le_norm _
  have compositionBound :
      ‖(closedFirstDerivative field (reflectedSpatialCell index candidate)).comp
          (fderiv ℝ (reflectedSpatialCell index) candidate)‖ ≤
        ‖closedFirstDerivativeDiskMap field‖ *
          ((2 * (‖fderiv ℝ normalizedSpatialCell point‖ + 1) + 1) *
            node index) := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul closedBound (reflectionBound index)
        (norm_nonneg (fderiv ℝ (reflectedSpatialCell index) candidate))
        (norm_nonneg (closedFirstDerivativeDiskMap field)))
  rw [exteriorSummandFirstModel]
  calc
    ‖exteriorScalar index candidate •
          (closedFirstDerivative field (reflectedSpatialCell index candidate)).comp
            (fderiv ℝ (reflectedSpatialCell index) candidate) +
        (fderiv ℝ (exteriorScalar index) candidate).smulRight
          (field.value (retractedDiskCell (reflectedSpatialCell index candidate)))‖ ≤
        ‖exteriorScalar index candidate •
          (closedFirstDerivative field (reflectedSpatialCell index candidate)).comp
            (fderiv ℝ (reflectedSpatialCell index) candidate)‖ +
        ‖(fderiv ℝ (exteriorScalar index) candidate).smulRight
          (field.value (retractedDiskCell (reflectedSpatialCell index candidate)))‖ :=
      norm_add_le _ _
    _ ≤ ‖exteriorScalar index candidate‖ *
          ‖(closedFirstDerivative field (reflectedSpatialCell index candidate)).comp
            (fderiv ℝ (reflectedSpatialCell index) candidate)‖ +
        ‖fderiv ℝ (exteriorScalar index) candidate‖ *
          ‖field.value (retractedDiskCell (reflectedSpatialCell index candidate))‖ := by
      exact add_le_add (le_of_eq (norm_smul _ _))
        (norm_complex_smulRight_le _ _)
    _ ≤ |coefficient index| *
          (‖closedFirstDerivativeDiskMap field‖ *
            ((2 * (‖fderiv ℝ normalizedSpatialCell point‖ + 1) + 1) *
              node index)) +
        (|coefficient index| * plateauFirstBound * node index * ‖planarPartCLM‖) *
          ‖field.value‖ := by
      exact add_le_add
        (mul_le_mul scalarBound compositionBound (norm_nonneg _) (abs_nonneg _))
        (mul_le_mul scalarDerivativeBound sampleBound (norm_nonneg _)
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (abs_nonneg _) plateauFirstBound_nonnegative)
              (node_positive index).le)
            (norm_nonneg _)))
    _ = exteriorFirstModelBoundConstant field point *
          (|coefficient index| * node index) := by
      unfold exteriorFirstModelBoundConstant
      ring

theorem exteriorSummandCellLift_hasFDerivAt {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : ℕ) (point : SpatialCell)
    (outside : 1 < ‖planarPart point‖) :
    HasFDerivAt (exteriorSummandCellLift field index)
      (exteriorSummandFirstModel field index point) point := by
  have planarNonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at outside
    linarith
  by_cases active : node index * (‖planarPart point‖ - 1) ≤ cutoffSupportWidth
  · have activeRange : node index * (‖planarPart point‖ - 1) < 1 := by
      rw [collar_constants.2.2.1] at active
      linarith
    have mappedMembership :=
      reflectedSpatialCell_mem_openUnitCylinder index point outside activeRange
    have fieldSmoothAt : ContDiffAt ℝ ∞ (diskCellLift field.value)
        (reflectedSpatialCell index point) :=
      (field.smoothInterior _ mappedMembership).contDiffAt
        (openUnitCylinder_isOpen.mem_nhds mappedMembership)
    have fieldDerivative : HasFDerivAt (diskCellLift field.value)
        (closedFirstDerivative field (reflectedSpatialCell index point))
        (reflectedSpatialCell index point) := by
      rw [closedFirstDerivative_eq_fderiv field _ mappedMembership]
      exact (fieldSmoothAt.differentiableAt (by simp)).hasFDerivAt
    have reflectedDerivative :=
      ((reflectedSpatialCell_contDiffAt index point planarNonzero).differentiableAt
        (by simp)).hasFDerivAt
    have sampleDerivative := fieldDerivative.comp point reflectedDerivative
    have scalarDerivative :=
      ((exteriorScalar_contDiffAt index point planarNonzero).differentiableAt
        (by simp)).hasFDerivAt
    have productDerivative := scalarDerivative.smul sampleDerivative
    rw [show exteriorSummandCellLift field index = fun candidate =>
        exteriorScalar index candidate •
          diskCellLift field.value (reflectedSpatialCell index candidate) by
      funext candidate
      exact exteriorSummandCellLift_formula field index candidate]
    rw [exteriorSummandFirstModel,
      ← diskCellLift_eq_retractedDiskCell field (reflectedSpatialCell index point)
        (openCylinderMembershipClosed _ mappedMembership)]
    exact productDerivative
  · have strictInactive : cutoffSupportWidth <
        node index * (‖planarPart point‖ - 1) := lt_of_not_ge active
    have scaleContinuousAt : ContinuousAt
        (fun candidate : SpatialCell =>
          node index * (‖planarPart candidate‖ - 1)) point :=
      ((contDiffAt_norm_planarPart point planarNonzero).continuousAt.sub
        continuousAt_const).const_mul _
    have eventuallyInactive : ∀ᶠ candidate in 𝓝 point,
        cutoffSupportWidth ≤ node index * (‖planarPart candidate‖ - 1) :=
      (scaleContinuousAt.eventually (Ioi_mem_nhds strictInactive)).mono
        fun _ inequality => inequality.le
    have scalarZero : exteriorScalar index =ᶠ[𝓝 point] fun _ => (0 : ℂ) := by
      filter_upwards [eventuallyInactive] with candidate inactive
      simp [exteriorScalar, plateauCutoff_zero _ inactive]
    have summandZero : exteriorSummandCellLift field index =ᶠ[𝓝 point]
        fun _ => (0 : ComplexEuclidean dimension) := by
      filter_upwards [eventuallyInactive] with candidate inactive
      simp [exteriorSummandCellLift_formula, plateauCutoff_zero _ inactive]
    have scalarDerivativeZero : fderiv ℝ (exteriorScalar index) point = 0 := by
      have constantDerivative : HasFDerivAt
          (fun _ : SpatialCell => (0 : ℂ)) (0 : SpatialCell →L[ℝ] ℂ) point :=
        hasFDerivAt_const _ _
      exact (constantDerivative.congr_of_eventuallyEq scalarZero).fderiv
    have scalarValueZero : exteriorScalar index point = 0 := scalarZero.eq_of_nhds
    have modelZero : exteriorSummandFirstModel field index point = 0 := by
      simp [exteriorSummandFirstModel, scalarValueZero, scalarDerivativeZero]
      change (0 : ℂ) •
        ((closedFirstDerivative field (reflectedSpatialCell index point)).comp
          (fderiv ℝ (reflectedSpatialCell index) point)) = 0
      exact zero_smul ℂ
        ((closedFirstDerivative field (reflectedSpatialCell index point)).comp
          (fderiv ℝ (reflectedSpatialCell index) point))
    rw [modelZero]
    have constantDerivative : HasFDerivAt
        (fun _ : SpatialCell => (0 : ComplexEuclidean dimension))
        (0 : SpatialCell →L[ℝ] ComplexEuclidean dimension) point :=
      hasFDerivAt_const _ _
    exact constantDerivative.congr_of_eventuallyEq summandZero

theorem exteriorSeriesCellLift_hasFDerivAt {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (outside : 1 < ‖planarPart point‖) :
    HasFDerivAt (exteriorSeriesCellLift field)
      (∑' index, exteriorSummandFirstModel field index point) point := by
  obtain ⟨cutoff, neighborhood⟩ :=
    eventually_common_exterior_tail_zero field point outside
  have finiteDerivative : HasFDerivAt
      (fun candidate =>
        ∑ index ∈ Finset.range cutoff, exteriorSummandCellLift field index candidate)
      (∑ index ∈ Finset.range cutoff, exteriorSummandFirstModel field index point) point := by
    exact HasFDerivAt.fun_sum fun index _ =>
      exteriorSummandCellLift_hasFDerivAt field index point outside
  have functionEquality : exteriorSeriesCellLift field =ᶠ[𝓝 point]
      fun candidate =>
        ∑ index ∈ Finset.range cutoff, exteriorSummandCellLift field index candidate := by
    filter_upwards [neighborhood] with candidate tail
    exact exteriorSeriesCellLift_eq_finite_sum_of_tail field cutoff candidate tail
  have seriesDerivative : HasFDerivAt (exteriorSeriesCellLift field)
      (∑ index ∈ Finset.range cutoff, exteriorSummandFirstModel field index point) point :=
    finiteDerivative.congr_of_eventuallyEq functionEquality
  have modelTailZero : ∀ index, cutoff ≤ index →
      exteriorSummandFirstModel field index point = 0 := by
    intro index indexBound
    have summandZero : exteriorSummandCellLift field index =ᶠ[𝓝 point]
        fun _ => (0 : ComplexEuclidean dimension) := by
      filter_upwards [neighborhood] with candidate tail
      exact tail index indexBound
    have zeroDerivative : fderiv ℝ (exteriorSummandCellLift field index) point = 0 := by
      have constantDerivative : HasFDerivAt
          (fun _ : SpatialCell => (0 : ComplexEuclidean dimension))
          (0 : SpatialCell →L[ℝ] ComplexEuclidean dimension) point :=
        hasFDerivAt_const _ _
      exact (constantDerivative.congr_of_eventuallyEq summandZero).fderiv
    have modelDerivative :=
      (exteriorSummandCellLift_hasFDerivAt field index point outside).fderiv
    rw [zeroDerivative] at modelDerivative
    exact modelDerivative.symm
  have modelSeriesEquality :
      ∑' index, exteriorSummandFirstModel field index point =
        ∑ index ∈ Finset.range cutoff, exteriorSummandFirstModel field index point :=
    (hasSum_sum_of_ne_finset_zero fun index outsideRange =>
      modelTailZero index (by simpa using outsideRange)).tsum_eq
  rw [modelSeriesEquality]
  exact seriesDerivative

theorem exteriorSeriesCellLift_fderiv {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (outside : 1 < ‖planarPart point‖) :
    fderiv ℝ (exteriorSeriesCellLift field) point =
      ∑' index, exteriorSummandFirstModel field index point :=
  (exteriorSeriesCellLift_hasFDerivAt field point outside).fderiv

def exteriorTangentBall (point : SpatialCell) : Set SpatialCell :=
  planarPartCLM ⁻¹' Metric.ball ((2 : ℝ) • planarPart point) 1

theorem exteriorTangentBall_isOpen (point : SpatialCell) :
    IsOpen (exteriorTangentBall point) := by
  exact Metric.isOpen_ball.preimage planarPartCLM.continuous

theorem exteriorTangentBall_convex (point : SpatialCell) :
    Convex ℝ (exteriorTangentBall point) := by
  exact (convex_ball ((2 : ℝ) • planarPart point) 1).linear_preimage planarPartLinear

theorem exteriorTangentBall_subset_outerOpen (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    exteriorTangentBall point ⊆
      {candidate : SpatialCell | 1 < ‖planarPart candidate‖} := by
  intro candidate membership
  change dist (planarPart candidate) ((2 : ℝ) • planarPart point) < 1 at membership
  have triangle := dist_triangle ((2 : ℝ) • planarPart point) (planarPart candidate) 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    boundary, mul_one, dist_comm ((2 : ℝ) • planarPart point) (planarPart candidate),
    dist_zero_right] at triangle
  change 1 < ‖planarPart candidate‖
  linarith

theorem closure_exteriorTangentBall (point : SpatialCell) :
    closure (exteriorTangentBall point) =
      planarPartCLM ⁻¹' Metric.closedBall ((2 : ℝ) • planarPart point) 1 := by
  rw [exteriorTangentBall,
    planarPartCLM.closure_preimage planarPartCLM_surjective,
    closure_ball ((2 : ℝ) • planarPart point) (by norm_num : (1 : ℝ) ≠ 0)]

theorem boundary_mem_closure_exteriorTangentBall (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    point ∈ closure (exteriorTangentBall point) := by
  rw [closure_exteriorTangentBall]
  change dist (planarPart point) ((2 : ℝ) • planarPart point) ≤ 1
  rw [dist_eq_norm, show planarPart point - (2 : ℝ) • planarPart point =
    -planarPart point by module, norm_neg, boundary]

theorem closure_exteriorTangentBall_subset_outerClosed (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    closure (exteriorTangentBall point) ⊆
      {candidate : SpatialCell | 1 ≤ ‖planarPart candidate‖} := by
  intro candidate membership
  rw [closure_exteriorTangentBall] at membership
  change dist (planarPart candidate) ((2 : ℝ) • planarPart point) ≤ 1 at membership
  have triangle := dist_triangle ((2 : ℝ) • planarPart point) (planarPart candidate) 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    boundary, mul_one, dist_comm ((2 : ℝ) • planarPart point) (planarPart candidate),
    dist_zero_right] at triangle
  change 1 ≤ ‖planarPart candidate‖
  linarith

def radialSpatialDirection (point : SpatialCell) : SpatialCell :=
  assembleSpatialCell (planarPart point) 0

def radialSpatialLine (point : SpatialCell) (scale : ℝ) : SpatialCell :=
  point + scale • radialSpatialDirection point

theorem planarPart_radialSpatialLine (point : SpatialCell) (scale : ℝ) :
    planarPart (radialSpatialLine point scale) =
      (1 + scale) • planarPart point := by
  ext coordinate
  fin_cases coordinate <;>
    simp [radialSpatialLine, radialSpatialDirection, planarPart, assembleSpatialCell] <;>
    ring

theorem radialSpatialLine_cell (point : SpatialCell) (scale : ℝ) :
    radialSpatialLine point scale 2 = point 2 := by
  simp [radialSpatialLine, radialSpatialDirection, assembleSpatialCell]

theorem radialSpatialLine_hasDerivAt (point : SpatialCell) :
    HasDerivAt (radialSpatialLine point) (radialSpatialDirection point) 0 := by
  rw [hasDerivAt_iff_hasFDerivAt, ← hasFDerivWithinAt_univ,
    hasFDerivWithinAt_piLp]
  intro coordinate
  change HasFDerivWithinAt (fun scale : ℝ =>
    point coordinate + scale * radialSpatialDirection point coordinate)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (radialSpatialDirection point coordinate)) Set.univ 0
  fun_prop

theorem radialSpatialLine_right_mapsTo_tangentClosure (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    MapsTo (radialSpatialLine point) (Icc (0 : ℝ) 1)
      (closure (exteriorTangentBall point)) := by
  intro scale scaleMembership
  rw [closure_exteriorTangentBall]
  change dist (planarPart (radialSpatialLine point scale))
    ((2 : ℝ) • planarPart point) ≤ 1
  rw [planarPart_radialSpatialLine, dist_eq_norm,
    show (1 + scale) • planarPart point - (2 : ℝ) • planarPart point =
      (scale - 1) • planarPart point by module,
    norm_smul, Real.norm_eq_abs, boundary, mul_one]
  exact abs_le.mpr ⟨by linarith [scaleMembership.1], by linarith [scaleMembership.2]⟩

theorem radialSpatialLine_left_mapsTo_closedCylinder (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    MapsTo (radialSpatialLine point) (Icc (-(1 / 2 : ℝ)) 0) closedUnitCylinder := by
  intro scale scaleMembership
  change ‖planarPart (radialSpatialLine point scale)‖ ≤ 1
  rw [planarPart_radialSpatialLine, norm_smul, Real.norm_eq_abs, boundary, mul_one,
    abs_of_nonneg (by linarith [scaleMembership.1])]
  linarith [scaleMembership.2]

theorem ambientExtensionCellLift_eq_diskCellLift {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (membership : point ∈ closedUnitCylinder) :
    ambientExtensionCellLift field point = diskCellLift field.value point := by
  change ‖planarPart point‖ ≤ 1 at membership
  rw [ambientExtensionCellLift_eq_if field point, if_pos membership,
    diskCellLift_eq_retractedDiskCell field point membership]

theorem ambientExtensionCellLift_eq_exteriorSeries {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (outside : 1 ≤ ‖planarPart point‖) :
    ambientExtensionCellLift field point = exteriorSeriesCellLift field point := by
  by_cases boundary : ‖planarPart point‖ = 1
  · rw [ambientExtensionCellLift_eq_if field point, if_pos boundary.le,
      retractedDiskCell_eq_diskCellPoint point boundary.le]
    exact (exteriorSeries_boundary field (planarPart point) boundary
      (point 2 : CellCircle)).symm
  · have notInside : ¬‖planarPart point‖ ≤ 1 := by
      intro inside
      exact boundary (le_antisymm inside outside)
    rw [ambientExtensionCellLift_eq_if field point, if_neg notInside]

theorem reflectedSpatialCell_boundary (index : ℕ) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    reflectedSpatialCell index point = point := by
  ext coordinate
  fin_cases coordinate
  · change (reflectedPoint index (planarPart point)) 0 = point 0
    rw [reflectedPoint_boundary index (planarPart point) boundary]
    rfl
  · change (reflectedPoint index (planarPart point)) 1 = point 1
    rw [reflectedPoint_boundary index (planarPart point) boundary]
    rfl
  · rfl

theorem exteriorSummandFirstModel_boundary {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : ℕ) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    exteriorSummandFirstModel field index point =
      coefficient index •
        (closedFirstDerivative field point).comp
          (fderiv ℝ (reflectedSpatialCell index) point) := by
  have scalarEquality : exteriorScalar index point = (coefficient index : ℂ) :=
    (exteriorScalar_eventually_boundary index point boundary).eq_of_nhds
  rw [exteriorSummandFirstModel, scalarEquality,
    reflectedSpatialCell_boundary index point boundary,
    exteriorScalar_fderiv_boundary index point boundary]
  simp
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) (coefficient index)
    ((closedFirstDerivative field point).comp
      (fderiv ℝ (reflectedSpatialCell index) point))).symm

theorem exteriorSummandFirstModel_continuousAt_boundary {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : ℕ) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    ContinuousAt (exteriorSummandFirstModel field index) point := by
  have planarNonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at boundary
    norm_num at boundary
  have reflectedSmooth := reflectedSpatialCell_contDiffAt index point planarNonzero
  have reflectedContinuous : ContinuousAt (reflectedSpatialCell index) point :=
    reflectedSmooth.continuousAt
  have reflectedDerivativeContinuous : ContinuousAt
      (fun candidate => fderiv ℝ (reflectedSpatialCell index) candidate) point :=
    reflectedSmooth.continuousAt_fderiv (by simp)
  have scalarSmooth := exteriorScalar_contDiffAt index point planarNonzero
  have scalarContinuous : ContinuousAt (exteriorScalar index) point :=
    scalarSmooth.continuousAt
  have scalarDerivativeContinuous : ContinuousAt
      (fun candidate => fderiv ℝ (exteriorScalar index) candidate) point :=
    scalarSmooth.continuousAt_fderiv (by simp)
  have closedDerivativeContinuous : ContinuousAt
      (fun candidate => closedFirstDerivative field
        (reflectedSpatialCell index candidate)) point :=
    (closedFirstDerivative_continuous field).continuousAt.comp reflectedContinuous
  have sampleContinuous : ContinuousAt
      (fun candidate => field.value
        (retractedDiskCell (reflectedSpatialCell index candidate))) point :=
    field.value.continuous.continuousAt.comp
      (continuous_retractedDiskCell.continuousAt.comp reflectedContinuous)
  let scalarAction : (ComplexEuclidean dimension) →L[ℝ]
      ℂ →L[ℝ] ComplexEuclidean dimension :=
    (ContinuousLinearMap.lsmul ℝ ℂ).flip
  have secondTermContinuous : ContinuousAt (fun candidate =>
      (scalarAction
        (field.value (retractedDiskCell (reflectedSpatialCell index candidate)))).comp
          (fderiv ℝ (exteriorScalar index) candidate)) point := by
    fun_prop
  have secondTermEquality : (fun candidate =>
      (fderiv ℝ (exteriorScalar index) candidate).smulRight
        (field.value (retractedDiskCell (reflectedSpatialCell index candidate)))) =
      fun candidate =>
        (scalarAction
          (field.value (retractedDiskCell (reflectedSpatialCell index candidate)))).comp
            (fderiv ℝ (exteriorScalar index) candidate) := by
    funext candidate
    ext direction
    rfl
  have originalSecondTermContinuous : ContinuousAt (fun candidate =>
      (fderiv ℝ (exteriorScalar index) candidate).smulRight
        (field.value (retractedDiskCell (reflectedSpatialCell index candidate)))) point := by
    rw [secondTermEquality]
    exact secondTermContinuous
  have firstTermContinuous : ContinuousAt (fun candidate =>
      exteriorScalar index candidate •
        (closedFirstDerivative field (reflectedSpatialCell index candidate)).comp
          (fderiv ℝ (reflectedSpatialCell index) candidate)) point := by
    fun_prop
  unfold exteriorSummandFirstModel
  exact firstTermContinuous.add originalSecondTermContinuous

theorem exteriorSummandFirstModel_boundary_tsum {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    ∑' index, exteriorSummandFirstModel field index point =
      closedFirstDerivative field point := by
  have nonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at boundary
    norm_num at boundary
  simp_rw [exteriorSummandFirstModel_boundary field _ point boundary]
  exact coefficient_closedFirstDerivative_reflection_tsum field point nonzero

theorem exteriorFirstModel_tendsto_boundary {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    Tendsto (fun candidate =>
      ∑' index, exteriorSummandFirstModel field index candidate)
      (𝓝 point) (𝓝 (closedFirstDerivative field point)) := by
  have convergence : Tendsto (fun candidate =>
      ∑' index, exteriorSummandFirstModel field index candidate)
      (𝓝 point)
      (𝓝 (∑' index, exteriorSummandFirstModel field index point)) := by
    apply tendsto_tsum_of_dominated_convergence
      (exteriorFirstModel_majorant_summable field point)
    · intro index
      exact (exteriorSummandFirstModel_continuousAt_boundary
        field index point boundary).tendsto
    · exact eventually_exteriorSummandFirstModel_norm_le_boundary field point boundary
  rw [exteriorSummandFirstModel_boundary_tsum field point boundary] at convergence
  exact convergence

theorem exteriorSeriesCellLift_hasFDerivWithinAt_tangentClosure {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    HasFDerivWithinAt (exteriorSeriesCellLift field)
      (closedFirstDerivative field point) (closure (exteriorTangentBall point)) point := by
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
  · intro candidate membership
    exact (exteriorSeriesCellLift_contDiffAt field candidate
      (exteriorTangentBall_subset_outerOpen point boundary membership)).differentiableAt
        (by simp) |>.differentiableWithinAt
  · exact exteriorTangentBall_convex point
  · exact exteriorTangentBall_isOpen point
  · intro candidate candidateClosure
    have subsetClosed : exteriorTangentBall point ⊆
        {candidate : SpatialCell | 1 ≤ ‖planarPart candidate‖} := by
      intro other otherMembership
      change 1 ≤ ‖planarPart other‖
      exact (exteriorTangentBall_subset_outerOpen point boundary otherMembership :
        1 < ‖planarPart other‖).le
    exact (exteriorSeriesCellLift_continuousOn_outerClosed field candidate
      (closure_exteriorTangentBall_subset_outerClosed point boundary candidateClosure)).mono
        subsetClosed
  · apply ((exteriorFirstModel_tendsto_boundary field point boundary).mono_left
      inf_le_left).congr'
    filter_upwards [self_mem_nhdsWithin] with candidate membership
    exact (exteriorSeriesCellLift_fderiv field candidate
      (exteriorTangentBall_subset_outerOpen point boundary membership)).symm

theorem ambientExtensionCellLift_hasDerivAt_radial_boundary {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    HasDerivAt (ambientExtensionCellLift field ∘ radialSpatialLine point)
      (closedFirstDerivative field point (radialSpatialDirection point)) 0 := by
  have lineDerivative := radialSpatialLine_hasDerivAt point
  have rightExterior : HasDerivWithinAt
      (exteriorSeriesCellLift field ∘ radialSpatialLine point)
      (closedFirstDerivative field point (radialSpatialDirection point))
      (Icc (0 : ℝ) 1) 0 :=
    (exteriorSeriesCellLift_hasFDerivWithinAt_tangentClosure field point boundary).comp_hasDerivWithinAt_of_eq
      0 lineDerivative.hasDerivWithinAt
        (radialSpatialLine_right_mapsTo_tangentClosure point boundary)
          (by simp [radialSpatialLine])
  have rightAmbient : HasDerivWithinAt
      (ambientExtensionCellLift field ∘ radialSpatialLine point)
      (closedFirstDerivative field point (radialSpatialDirection point))
      (Icc (0 : ℝ) 1) 0 := by
    apply rightExterior.congr
    · intro scale scaleMembership
      apply ambientExtensionCellLift_eq_exteriorSeries
      rw [planarPart_radialSpatialLine, norm_smul, Real.norm_eq_abs, boundary, mul_one,
        abs_of_nonneg (by linarith [scaleMembership.1])]
      linarith [scaleMembership.1]
    · simp only [Function.comp_apply]
      apply ambientExtensionCellLift_eq_exteriorSeries
      simp [radialSpatialLine, boundary]
  have leftDisk : HasDerivWithinAt
      (diskCellLift field.value ∘ radialSpatialLine point)
      (closedFirstDerivative field point (radialSpatialDirection point))
      (Icc (-(1 / 2 : ℝ)) 0) 0 :=
    (diskCellLift_hasFDerivWithinAt_closed field point).comp_hasDerivWithinAt_of_eq
      0 lineDerivative.hasDerivWithinAt
        (radialSpatialLine_left_mapsTo_closedCylinder point boundary)
          (by simp [radialSpatialLine])
  have leftAmbient : HasDerivWithinAt
      (ambientExtensionCellLift field ∘ radialSpatialLine point)
      (closedFirstDerivative field point (radialSpatialDirection point))
      (Icc (-(1 / 2 : ℝ)) 0) 0 := by
    apply leftDisk.congr
    · intro scale scaleMembership
      apply ambientExtensionCellLift_eq_diskCellLift
      exact radialSpatialLine_left_mapsTo_closedCylinder point boundary scaleMembership
    · simp only [Function.comp_apply]
      apply ambientExtensionCellLift_eq_diskCellLift
      change ‖planarPart (radialSpatialLine point 0)‖ ≤ 1
      simp [planarPart_radialSpatialLine, boundary]
  have unionDerivative := leftAmbient.union rightAmbient
  apply unionDerivative.hasDerivAt
  apply mem_of_superset (Ioo_mem_nhds (by norm_num : (-(1 / 2 : ℝ)) < 0)
    (by norm_num : (0 : ℝ) < 1))
  intro scale scaleMembership
  by_cases nonpositive : scale ≤ 0
  · exact Or.inl ⟨scaleMembership.1.le, nonpositive⟩
  · exact Or.inr ⟨le_of_not_ge nonpositive, scaleMembership.2.le⟩

end Grad.DiskExtension.Operator
