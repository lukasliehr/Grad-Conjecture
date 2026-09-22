import GC13Orthogonal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Convex.Integral

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 1000000

open Set MeasureTheory
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators ENNReal Topology

namespace Grad.GaugeCoefficients.Radial

open Grad.GaugeCoefficients.Algebra
open Grad.RepresentedKernel.SpatialProduct

theorem planeRotation_neg_left (angle : ℝ) (point : SpatialPlane) :
    planeRotation (-angle) (planeRotation angle point) = point := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · change Real.cos (-angle) *
        (Real.cos angle * point 0 - Real.sin angle * point 1) -
      Real.sin (-angle) *
        (Real.sin angle * point 0 + Real.cos angle * point 1) = point 0
    rw [Real.cos_neg, Real.sin_neg]
    calc
      _ = (Real.cos angle ^ 2 + Real.sin angle ^ 2) * point 0 := by ring
      _ = point 0 := by
        rw [show Real.cos angle ^ 2 + Real.sin angle ^ 2 = 1 by
          nlinarith [Real.sin_sq_add_cos_sq angle]]
        ring
  · change Real.sin (-angle) *
        (Real.cos angle * point 0 - Real.sin angle * point 1) +
      Real.cos (-angle) *
        (Real.sin angle * point 0 + Real.cos angle * point 1) = point 1
    rw [Real.cos_neg, Real.sin_neg]
    calc
      _ = (Real.sin angle ^ 2 + Real.cos angle ^ 2) * point 1 := by ring
      _ = point 1 := by rw [Real.sin_sq_add_cos_sq]; ring

theorem planeRotation_neg_right (angle : ℝ) (point : SpatialPlane) :
    planeRotation angle (planeRotation (-angle) point) = point := by
  simpa only [neg_neg] using planeRotation_neg_left (-angle) point

def planeRotationEquiv (angle : ℝ) : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane where
  toFun := planeRotation angle
  map_add' first second := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [planeRotation] <;> ring
  map_smul' scalar point := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [planeRotation] <;> ring
  norm_map' := planeRotation_norm angle
  invFun := planeRotation (-angle)
  left_inv := planeRotation_neg_left angle
  right_inv := planeRotation_neg_right angle

@[simp] theorem planeRotationEquiv_apply (angle : ℝ) (point : SpatialPlane) :
    planeRotationEquiv angle point = planeRotation angle point := rfl

theorem orthogonalClosedPoint_rotation (angle : ℝ) (point : ClosedDisk) :
    orthogonalClosedPoint (planeRotationEquiv angle) point =
      rotatedPoint angle point := by
  apply Subtype.ext
  rfl

theorem continuous_planeRotation_joint :
    Continuous (fun pair : ℝ × SpatialPlane => planeRotation pair.1 pair.2) := by
  unfold planeRotation
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  fun_prop

theorem continuous_rotatedPoint_joint :
    Continuous (fun pair : ℝ × ClosedDisk => rotatedPoint pair.1 pair.2) := by
  apply continuous_induced_rng.mpr
  exact continuous_planeRotation_joint.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

theorem continuous_planeRotationEquiv_entry
    (direction coordinate : Fin 2) :
    Continuous (fun angle : ℝ =>
      planeRotationEquiv angle (spatialDirection direction) coordinate) := by
  fin_cases direction <;> fin_cases coordinate <;>
    simp [planeRotationEquiv, planeRotation, spatialDirection] <;> fun_prop

theorem continuous_rotation_chainFactor (rank : ℕ)
    (word target : Word rank) :
    Continuous (fun angle : ℝ =>
      chainFactor rank (planeRotationEquiv angle) word target) := by
  simp only [chainFactor_eq]
  apply continuous_finsetProd
  intro position _membership
  exact continuous_planeRotationEquiv_entry (word position) (target position)

def rawRotationTermJoint {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade)
    (target : Word (derivativeOrder index)) :
    C(ℝ × ClosedDisk, OperatorValue inputDimension outputDimension) where
  toFun pair := rawOrthogonalTerm
    (planeRotationEquiv (2 * Real.pi * pair.1)) coefficient cell index target pair.2
  continuous_toFun := by
    unfold rawOrthogonalTerm orthogonalClosedMap
    exact (Complex.continuous_ofReal.comp
      ((continuous_rotation_chainFactor (derivativeOrder index)
        (derivativeWord index) target).comp
          (continuous_const.mul continuous_fst))).smul
      ((coefficient (cell, orthogonalDerivativeIndex index target)).continuous.comp
        (continuous_rotatedPoint_joint.comp
          ((continuous_const.mul continuous_fst).prodMk continuous_snd)))

def rawRotationCoordinateJoint
    {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    C(ℝ × ClosedDisk, OperatorValue inputDimension outputDimension) :=
  ∑ target : Word (derivativeOrder index),
    rawRotationTermJoint coefficient cell index target

@[simp] theorem rawRotationCoordinateJoint_apply
    {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (time : ℝ) (point : ClosedDisk) :
    rawRotationCoordinateJoint coefficient cell index (time, point) =
      rawOrthogonalCoordinate (planeRotationEquiv (2 * Real.pi * time))
        coefficient cell index point := by
  unfold rawRotationCoordinateJoint rawOrthogonalCoordinate
  rw [continuousMap_sum_apply, continuousMap_sum_apply]
  rfl

def rawAngularCoordinate {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) where
  toFun point := ∫ time in Icc (0 : ℝ) 1,
    rawRotationCoordinateJoint coefficient cell index (time, point)
  continuous_toFun := by
    apply continuous_parametric_integral_of_continuous
    exact (rawRotationCoordinateJoint coefficient cell index).continuous.comp
      (continuous_snd.prodMk continuous_fst)
    exact isCompact_Icc

theorem rawAngularCoordinate_norm_le
    {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    ‖rawAngularCoordinate coefficient cell index‖ ≤
      ∑ target : Word (derivativeOrder index),
        ‖coefficient (cell, orthogonalDerivativeIndex index target)‖ := by
  let bound : ℝ := ∑ target : Word (derivativeOrder index),
    ‖coefficient (cell, orthogonalDerivativeIndex index target)‖
  apply (ContinuousMap.norm_le _ (Finset.sum_nonneg fun target _ => norm_nonneg
    (coefficient (cell, orthogonalDerivativeIndex index target)))).2
  intro point
  change ‖∫ time in Icc (0 : ℝ) 1,
      rawRotationCoordinateJoint coefficient cell index (time, point)‖ ≤ bound
  have volumeReal : volume.real (Icc (0 : ℝ) 1) = 1 := by
    rw [Measure.real, Real.volume_Icc]
    norm_num
  calc
    _ ≤ bound * volume.real (Icc (0 : ℝ) 1) :=
      norm_setIntegral_le_of_norm_le_const
        (lt_top_iff_ne_top.mpr isCompact_Icc.measure_ne_top) (fun time _membership => by
        rw [rawRotationCoordinateJoint_apply]
        exact (ContinuousMap.norm_coe_le_norm
          (rawOrthogonalCoordinate (planeRotationEquiv (2 * Real.pi * time))
            coefficient cell index) point).trans
          (rawOrthogonalCoordinate_norm_le
            (planeRotationEquiv (2 * Real.pi * time)) coefficient cell index))
    _ = bound := by rw [volumeReal, mul_one]

def rawAngular {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension) :
    WeightedAmbient grade inputDimension outputDimension := by
  refine ⟨fun pair => rawAngularCoordinate coefficient pair.1 pair.2, ?_⟩
  apply memℓp_gen
  have each (index : DerivativeIndex grade) : Summable (fun cell : ℤ =>
      ‖rawAngularCoordinate coefficient cell index‖) :=
    Summable.of_nonneg_of_le
      (fun cell : ℤ => norm_nonneg (rawAngularCoordinate coefficient cell index))
      (fun cell => rawAngularCoordinate_norm_le coefficient cell index)
      (hasSum_sum (fun target _ => (coordinate_norm_summable coefficient
        (orthogonalDerivativeIndex index target)).hasSum)).summable
  have swapped : Summable (fun pair : DerivativeIndex grade × ℤ =>
      ‖rawAngularCoordinate coefficient pair.2 pair.1‖) := by
    apply (summable_prod_of_nonneg (fun pair : DerivativeIndex grade × ℤ =>
      norm_nonneg (rawAngularCoordinate coefficient pair.2 pair.1))).2
    exact ⟨each, (hasSum_fintype _).summable⟩
  have all : Summable (fun pair : ℤ × DerivativeIndex grade =>
      ‖rawAngularCoordinate coefficient pair.1 pair.2‖) := by
    apply (Equiv.prodComm (DerivativeIndex grade) ℤ).summable_iff.mp
    exact swapped
  have oneToReal : (1 : ℝ≥0∞).toReal = 1 := by norm_num
  simpa only [oneToReal, Real.rpow_one] using all

@[simp] theorem rawAngular_apply {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    rawAngular coefficient (cell, index) =
      rawAngularCoordinate coefficient cell index := rfl

theorem rawAngular_norm_le {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension) :
    ‖rawAngular coefficient‖ ≤ angularBound grade * ‖coefficient‖ := by
  rw [ambient_norm_formula]
  calc
    (∑ index : DerivativeIndex grade, ∑' cell : ℤ,
      ‖rawAngular coefficient (cell, index)‖) ≤
        ∑ index : DerivativeIndex grade,
          ∑ target : Word (derivativeOrder index), ‖coefficient‖ := by
      apply Finset.sum_le_sum
      intro index _membership
      calc
        (∑' cell : ℤ, ‖rawAngular coefficient (cell, index)‖) ≤
            ∑' cell : ℤ, ∑ target : Word (derivativeOrder index),
              ‖coefficient (cell, orthogonalDerivativeIndex index target)‖ :=
          Summable.tsum_le_tsum
            (fun cell => rawAngularCoordinate_norm_le coefficient cell index)
            (coordinate_norm_summable (rawAngular coefficient) index)
            (hasSum_sum (fun target _ => (coordinate_norm_summable coefficient
              (orthogonalDerivativeIndex index target)).hasSum)).summable
        _ = ∑ target : Word (derivativeOrder index), ∑' cell : ℤ,
              ‖coefficient (cell, orthogonalDerivativeIndex index target)‖ := by
          rw [Summable.tsum_finsetSum (fun target _ =>
            coordinate_norm_summable coefficient
              (orthogonalDerivativeIndex index target))]
        _ ≤ ∑ _target : Word (derivativeOrder index), ‖coefficient‖ := by
          exact Finset.sum_le_sum fun target _ =>
            coordinate_norm_sum_le coefficient
              (orthogonalDerivativeIndex index target)
    _ ≤ ∑ _index : DerivativeIndex grade,
        (2 : ℝ) ^ grade * ‖coefficient‖ := by
      apply Finset.sum_le_sum
      intro index _membership
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg coefficient)
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) index.2
    _ = angularBound grade * ‖coefficient‖ := by
      simp [angularBound]
      ring

theorem rawRotationCoordinateJoint_add
    {grade inputDimension outputDimension : ℕ}
    (first second : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (time : ℝ) (point : ClosedDisk) :
    rawRotationCoordinateJoint (first + second) cell index (time, point) =
      rawRotationCoordinateJoint first cell index (time, point) +
        rawRotationCoordinateJoint second cell index (time, point) := by
  rw [rawRotationCoordinateJoint_apply, rawRotationCoordinateJoint_apply,
    rawRotationCoordinateJoint_apply]
  have linearity := (rawOrthogonalLinear grade inputDimension outputDimension
    (planeRotationEquiv (2 * Real.pi * time))).map_add first second
  exact congrArg (fun value : WeightedAmbient grade inputDimension outputDimension =>
    value (cell, index) point) linearity

theorem rawRotationCoordinateJoint_smul
    {grade inputDimension outputDimension : ℕ}
    (scalar : ℂ) (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (time : ℝ) (point : ClosedDisk) :
    rawRotationCoordinateJoint (scalar • coefficient) cell index (time, point) =
      scalar • rawRotationCoordinateJoint coefficient cell index (time, point) := by
  rw [rawRotationCoordinateJoint_apply, rawRotationCoordinateJoint_apply]
  have linearity := (rawOrthogonalLinear grade inputDimension outputDimension
    (planeRotationEquiv (2 * Real.pi * time))).map_smul scalar coefficient
  exact congrArg (fun value : WeightedAmbient grade inputDimension outputDimension =>
    value (cell, index) point) linearity

theorem rawAngularCoordinate_add
    {grade inputDimension outputDimension : ℕ}
    (first second : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    rawAngularCoordinate (first + second) cell index =
      rawAngularCoordinate first cell index + rawAngularCoordinate second cell index := by
  apply ContinuousMap.ext
  intro point
  have firstIntegrable : IntegrableOn
      (fun time : ℝ => rawRotationCoordinateJoint first cell index (time, point))
      (Icc 0 1) :=
    ((rawRotationCoordinateJoint first cell index).continuous.comp
      (continuous_id.prodMk continuous_const)).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have secondIntegrable : IntegrableOn
      (fun time : ℝ => rawRotationCoordinateJoint second cell index (time, point))
      (Icc 0 1) :=
    ((rawRotationCoordinateJoint second cell index).continuous.comp
      (continuous_id.prodMk continuous_const)).continuousOn
      |>.integrableOn_compact isCompact_Icc
  change (∫ time in Icc (0 : ℝ) 1,
      rawRotationCoordinateJoint (first + second) cell index (time, point)) =
    (∫ time in Icc (0 : ℝ) 1,
      rawRotationCoordinateJoint first cell index (time, point)) +
    ∫ time in Icc (0 : ℝ) 1,
      rawRotationCoordinateJoint second cell index (time, point)
  rw [← integral_add firstIntegrable secondIntegrable]
  apply integral_congr_ae
  filter_upwards with time
  exact rawRotationCoordinateJoint_add first second cell index time point

theorem rawAngularCoordinate_smul
    {grade inputDimension outputDimension : ℕ}
    (scalar : ℂ) (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    rawAngularCoordinate (scalar • coefficient) cell index =
      scalar • rawAngularCoordinate coefficient cell index := by
  apply ContinuousMap.ext
  intro point
  change (∫ time in Icc (0 : ℝ) 1,
      rawRotationCoordinateJoint (scalar • coefficient) cell index (time, point)) =
    scalar • ∫ time in Icc (0 : ℝ) 1,
      rawRotationCoordinateJoint coefficient cell index (time, point)
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with time
  exact rawRotationCoordinateJoint_smul scalar coefficient cell index time point

def rawAngularLinear (grade inputDimension outputDimension : ℕ) :
    WeightedAmbient grade inputDimension outputDimension →ₗ[ℂ]
      WeightedAmbient grade inputDimension outputDimension where
  toFun := rawAngular
  map_add' first second := by
    apply lp.ext
    funext pair
    exact rawAngularCoordinate_add first second pair.1 pair.2
  map_smul' scalar coefficient := by
    apply lp.ext
    funext pair
    exact rawAngularCoordinate_smul scalar coefficient pair.1 pair.2

def rawAngularMap (grade inputDimension outputDimension : ℕ) :
    WeightedAmbient grade inputDimension outputDimension →L[ℂ]
      WeightedAmbient grade inputDimension outputDimension :=
  (rawAngularLinear grade inputDimension outputDimension).mkContinuous
    (angularBound grade) rawAngular_norm_le

def rawRotationCoordinateCurve
    {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    ℝ → ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  fun time => rawOrthogonalCoordinate
    (planeRotationEquiv (2 * Real.pi * time)) coefficient cell index

theorem continuous_rawRotationCoordinateCurve
    {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    Continuous (rawRotationCoordinateCurve coefficient cell index) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun pair : ℝ × ClosedDisk =>
    rawRotationCoordinateCurve coefficient cell index pair.1 pair.2)
  rw [show (fun pair : ℝ × ClosedDisk =>
      rawRotationCoordinateCurve coefficient cell index pair.1 pair.2) =
        rawRotationCoordinateJoint coefficient cell index by
    funext pair
    exact (rawRotationCoordinateJoint_apply coefficient cell index
      pair.1 pair.2).symm]
  exact (rawRotationCoordinateJoint coefficient cell index).continuous

theorem rawOrthogonal_weightedSingle_eq_sum_single
    (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ} (cell : ℤ)
    (field : SmoothOperatorJet inputDimension outputDimension)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) :
    rawOrthogonal orthogonal
        (weightedSingle L sigma gamma ell grade cell field) =
      ∑ index : DerivativeIndex grade,
        (lp.single 1 (cell, index)
          (rawOrthogonalCoordinate orthogonal
            (weightedSingle L sigma gamma ell grade cell field) cell index) :
          WeightedAmbient grade inputDimension outputDimension) := by
  rw [rawOrthogonal_weightedSingle]
  change (∑ index : DerivativeIndex grade,
      (lp.single 1 (cell, index)
        (weightedSmoothDerivative L sigma gamma ell grade cell
          (orthogonalSmoothOperatorJet orthogonal field) index) :
        WeightedAmbient grade inputDimension outputDimension)) = _
  apply Finset.sum_congr rfl
  intro index _membership
  have coordinateEquality := congrArg
    (fun value : WeightedAmbient grade inputDimension outputDimension =>
      value (cell, index))
    (rawOrthogonal_weightedSingle L sigma gamma ell grade orthogonal cell field)
  rw [rawOrthogonal_apply, weightedSingle_apply_same] at coordinateEquality
  rw [coordinateEquality]

def rawRotationWeightedSingleCurve
    (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ} (cell : ℤ)
    (field : SmoothOperatorJet inputDimension outputDimension) :
    ℝ → WeightedAmbient grade inputDimension outputDimension :=
  fun time => rawOrthogonal (planeRotationEquiv (2 * Real.pi * time))
    (weightedSingle L sigma gamma ell grade cell field)

theorem continuous_rawRotationWeightedSingleCurve
    (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ} (cell : ℤ)
    (field : SmoothOperatorJet inputDimension outputDimension) :
    Continuous (rawRotationWeightedSingleCurve L sigma gamma ell grade cell field) := by
  have decomposition :
      rawRotationWeightedSingleCurve L sigma gamma ell grade cell field =
        fun time => ∑ index : DerivativeIndex grade,
          (lp.singleContinuousLinearMap ℂ
            (fun _ : ℤ × DerivativeIndex grade =>
              ContinuousMap ClosedDisk
                (OperatorValue inputDimension outputDimension)) 1 (cell, index))
            (rawRotationCoordinateCurve
              (weightedSingle L sigma gamma ell grade cell field) cell index time) := by
    funext time
    change rawOrthogonal (planeRotationEquiv (2 * Real.pi * time))
        (weightedSingle L sigma gamma ell grade cell field) = _
    rw [rawOrthogonal_weightedSingle_eq_sum_single]
    apply Finset.sum_congr rfl
    intro index _membership
    rw [lp.singleContinuousLinearMap_apply]
    rfl
  rw [decomposition]
  apply continuous_finsetSum
  intro index _membership
  exact (lp.singleContinuousLinearMap ℂ
      (fun _ : ℤ × DerivativeIndex grade =>
        ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension))
      1 (cell, index)).continuous.comp
    (continuous_rawRotationCoordinateCurve
      (weightedSingle L sigma gamma ell grade cell field) cell index)

theorem rawAngular_weightedSingle_mem_closure
    (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ} (cell : ℤ)
    (field : SmoothOperatorJet inputDimension outputDimension) :
    rawAngular (weightedSingle L sigma gamma ell grade cell field) ∈
      (smoothCore L sigma gamma ell grade
        inputDimension outputDimension).topologicalClosure := by
  let core := smoothCore L sigma gamma ell grade inputDimension outputDimension
  let orbit := rawRotationWeightedSingleCurve L sigma gamma ell grade cell field
  have orbitContinuous : Continuous orbit :=
    continuous_rawRotationWeightedSingleCurve L sigma gamma ell grade cell field
  have orbitIntegrable : IntegrableOn orbit (Icc (0 : ℝ) 1) :=
    orbitContinuous.continuousOn.integrableOn_compact isCompact_Icc
  have orbitMembership (time : ℝ) : orbit time ∈ core := by
    exact rawOrthogonal_mem_smoothCore L sigma gamma ell grade inputDimension
      outputDimension (planeRotationEquiv (2 * Real.pi * time))
        ⟨weightedSingle L sigma gamma ell grade cell field,
          Submodule.subset_span (Set.mem_range.mpr ⟨(cell, field), rfl⟩)⟩
  have integralMembership : (∫ time in Icc (0 : ℝ) 1, orbit time) ∈
      core.topologicalClosure := by
    let _ : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := by
      rw [isProbabilityMeasure_iff, Measure.restrict_apply_univ,
        Real.volume_Icc]
      norm_num
    have convexClosure : Convex ℝ (core.topologicalClosure : Set
        (WeightedAmbient grade inputDimension outputDimension)) := by
      change Convex ℝ
        (↑(core.topologicalClosure.restrictScalars ℝ) :
          Set (WeightedAmbient grade inputDimension outputDimension))
      exact (core.topologicalClosure.restrictScalars ℝ).convex
    exact Convex.integral_mem (μ := volume.restrict (Icc (0 : ℝ) 1))
      (f := orbit) convexClosure core.isClosed_topologicalClosure
      (by
        filter_upwards with time
        exact Submodule.le_topologicalClosure core (orbitMembership time))
      orbitIntegrable
  suffices equality : rawAngular
      (weightedSingle L sigma gamma ell grade cell field) =
        ∫ time in Icc (0 : ℝ) 1, orbit time by
    rw [equality]
    exact integralMembership
  apply lp.ext
  funext pair
  apply ContinuousMap.ext
  intro point
  let pointEvaluation :
      WeightedAmbient grade inputDimension outputDimension →L[ℂ]
        OperatorValue inputDimension outputDimension :=
    (ContinuousMap.evalCLM ℂ point).comp (lp.evalCLM ℂ
      (fun _ : ℤ × DerivativeIndex grade =>
        ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension))
      1 pair)
  change (∫ time in Icc (0 : ℝ) 1,
      rawRotationCoordinateJoint
        (weightedSingle L sigma gamma ell grade cell field)
          pair.1 pair.2 (time, point)) = pointEvaluation
            (∫ time in Icc (0 : ℝ) 1, orbit time)
  calc
    _ = ∫ time in Icc (0 : ℝ) 1, pointEvaluation (orbit time) := by
      apply integral_congr_ae
      filter_upwards with time
      rw [rawRotationCoordinateJoint_apply]
      rfl
    _ = pointEvaluation (∫ time in Icc (0 : ℝ) 1, orbit time) :=
      ContinuousLinearMap.integral_comp_comm (𝕜 := ℂ)
        pointEvaluation orbitIntegrable

theorem rawAngular_smoothCore_mem_closure
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (coefficient : smoothCore L sigma gamma ell grade
      inputDimension outputDimension) :
    rawAngular coefficient.1 ∈
      (smoothCore L sigma gamma ell grade
        inputDimension outputDimension).topologicalClosure := by
  let core := smoothCore L sigma gamma ell grade inputDimension outputDimension
  refine Submodule.span_induction
    (p := fun value _membership => rawAngular value ∈ core.topologicalClosure)
      ?generator ?zero ?add ?smul coefficient.2
  case generator =>
    intro generator membership
    rcases membership with ⟨pair, rfl⟩
    exact rawAngular_weightedSingle_mem_closure L sigma gamma ell grade
      pair.1 pair.2
  case zero =>
    change rawAngularLinear grade inputDimension outputDimension 0 ∈
      core.topologicalClosure
    rw [map_zero]
    exact core.topologicalClosure.zero_mem
  case add =>
    intro first second _ _ firstMembership secondMembership
    change rawAngularLinear grade inputDimension outputDimension
      (first + second) ∈ core.topologicalClosure
    rw [map_add]
    exact core.topologicalClosure.add_mem firstMembership secondMembership
  case smul =>
    intro scalar value _ valueMembership
    change rawAngularLinear grade inputDimension outputDimension
      (scalar • value) ∈ core.topologicalClosure
    rw [map_smul]
    exact core.topologicalClosure.smul_mem scalar valueMembership

theorem rawAngular_closure
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (coefficient : Coefficient L sigma gamma ell grade
      inputDimension outputDimension) :
    rawAngular coefficient.1 ∈
      (smoothCore L sigma gamma ell grade
        inputDimension outputDimension).topologicalClosure := by
  let core := smoothCore L sigma gamma ell grade inputDimension outputDimension
  let operation := rawAngularMap grade inputDimension outputDimension
  have coreMapLe : core.map (operation : _ →ₗ[ℂ] _) ≤
      core.topologicalClosure := by
    intro output membership
    rcases membership with ⟨input, inputMembership, rfl⟩
    exact rawAngular_smoothCore_mem_closure L sigma gamma ell grade
      inputDimension outputDimension ⟨input, inputMembership⟩
  have mapped : operation coefficient.1 ∈ core.topologicalClosure.map
      (operation : _ →ₗ[ℂ] _) := ⟨coefficient.1, coefficient.2, rfl⟩
  have twice : operation coefficient.1 ∈
      core.topologicalClosure.topologicalClosure :=
    (Submodule.topologicalClosure_mono coreMapLe)
      ((core.topologicalClosure_map operation) mapped)
  rw [core.isClosed_topologicalClosure.submodule_topologicalClosure_eq] at twice
  exact twice

def coefficientAngular
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (coefficient : Coefficient L sigma gamma ell grade
      inputDimension outputDimension) :
    Coefficient L sigma gamma ell grade inputDimension outputDimension :=
  ⟨rawAngular coefficient.1,
    rawAngular_closure L sigma gamma ell grade inputDimension
      outputDimension coefficient⟩

def coefficientAngularLinear
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ) :
    Coefficient L sigma gamma ell grade inputDimension outputDimension →ₗ[ℂ]
      Coefficient L sigma gamma ell grade inputDimension outputDimension where
  toFun := coefficientAngular L sigma gamma ell grade inputDimension outputDimension
  map_add' first second := by
    apply Subtype.ext
    exact (rawAngularLinear grade inputDimension outputDimension).map_add _ _
  map_smul' scalar coefficient := by
    apply Subtype.ext
    exact (rawAngularLinear grade inputDimension outputDimension).map_smul _ _

def coefficientAngularMap
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ) :
    Coefficient L sigma gamma ell grade inputDimension outputDimension →L[ℂ]
      Coefficient L sigma gamma ell grade inputDimension outputDimension :=
  (coefficientAngularLinear L sigma gamma ell grade inputDimension
    outputDimension).mkContinuous (angularBound grade)
      (fun coefficient => rawAngular_norm_le coefficient.1)

theorem coefficientAngular_bound
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (coefficient : Coefficient L sigma gamma ell grade
      inputDimension outputDimension) :
    ‖coefficientAngularMap L sigma gamma ell grade inputDimension
      outputDimension coefficient‖ ≤ angularBound grade * ‖coefficient‖ :=
  rawAngular_norm_le coefficient.1

theorem rawRotationCoordinateJoint_zero
    {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (time : ℝ) (point : ClosedDisk) :
    rawRotationCoordinateJoint coefficient cell (zeroDerivativeIndexAt grade)
        (time, point) =
      coefficient (cell, zeroDerivativeIndexAt grade)
        (rotatedPoint (2 * Real.pi * time) point) := by
  rw [rawRotationCoordinateJoint_apply]
  unfold rawOrthogonalCoordinate
  rw [continuousMap_sum_apply]
  let emptyWord : Word (derivativeOrder (zeroDerivativeIndexAt grade)) :=
    derivativeWord (zeroDerivativeIndexAt grade)
  have uniqueWord (target : Word
      (derivativeOrder (zeroDerivativeIndexAt grade))) : target = emptyWord := by
    apply funext
    intro position
    exact Fin.elim0 (show Fin 0 from by
      simpa [derivativeOrder, zeroDerivativeIndexAt] using position)
  calc
    (∑ target : Word (derivativeOrder (zeroDerivativeIndexAt grade)),
        rawOrthogonalTerm (planeRotationEquiv (2 * Real.pi * time))
          coefficient cell (zeroDerivativeIndexAt grade) target point) =
      rawOrthogonalTerm (planeRotationEquiv (2 * Real.pi * time))
        coefficient cell (zeroDerivativeIndexAt grade) emptyWord point := by
      apply Finset.sum_eq_single emptyWord
      · intro target _membership different
        exact (different (uniqueWord target)).elim
      · simp
    _ = _ := by
      have chainOne : chainFactor
          (derivativeOrder (zeroDerivativeIndexAt grade))
          (planeRotationEquiv (2 * Real.pi * time))
          (derivativeWord (zeroDerivativeIndexAt grade)) emptyWord = 1 := by
        rw [chainFactor_eq]
        apply Fintype.prod_eq_one
        intro position
        exact Fin.elim0 (show Fin 0 from by
          simpa [derivativeOrder, zeroDerivativeIndexAt] using position)
      have indexEquality : orthogonalDerivativeIndex
          (zeroDerivativeIndexAt grade) emptyWord =
            zeroDerivativeIndexAt grade := by
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext
        · change Grad.WeakTesting.Commutation.directionCount emptyWord 0 = 0
          have total := count_total
            (derivativeOrder (zeroDerivativeIndexAt grade)) emptyWord
          change Grad.WeakTesting.Commutation.directionCount emptyWord 0 +
            Grad.WeakTesting.Commutation.directionCount emptyWord 1 = 0 at total
          omega
        · change Grad.WeakTesting.Commutation.directionCount emptyWord 1 = 0
          have total := count_total
            (derivativeOrder (zeroDerivativeIndexAt grade)) emptyWord
          change Grad.WeakTesting.Commutation.directionCount emptyWord 0 +
            Grad.WeakTesting.Commutation.directionCount emptyWord 1 = 0 at total
          omega
      unfold rawOrthogonalTerm
      rw [chainOne, indexEquality]
      change (1 : ℂ) • coefficient (cell, zeroDerivativeIndexAt grade)
          (orthogonalClosedPoint (planeRotationEquiv (2 * Real.pi * time)) point) = _
      rw [one_smul, orthogonalClosedPoint_rotation]

theorem coefficientAngular_value
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (coefficient : Coefficient L sigma gamma ell grade
      inputDimension outputDimension)
    (cell : ℤ) (point : ClosedDisk) :
    coefficientDerivative
        (coefficientAngularMap L sigma gamma ell grade inputDimension
          outputDimension coefficient) cell (zeroDerivativeIndexAt grade) point =
      angularMeanValue coefficient cell point := by
  unfold coefficientDerivative weightedDerivative angularMeanValue
  change ((coefficientScale L sigma gamma ell grade cell
      (zeroDerivativeIndexAt grade) point : ℂ)⁻¹) •
      (∫ time in Icc (0 : ℝ) 1,
        rawRotationCoordinateJoint coefficient.1 cell
          (zeroDerivativeIndexAt grade) (time, point)) = _
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with time
  rw [rawRotationCoordinateJoint_zero]
  change ((coefficientScale L sigma gamma ell grade cell
      (zeroDerivativeIndexAt grade) point : ℂ)⁻¹) •
        coefficient.1 (cell, zeroDerivativeIndexAt grade)
          (rotatedPoint (2 * Real.pi * time) point) = _
  change ((coefficientScale L sigma gamma ell grade cell
      (zeroDerivativeIndexAt grade) point : ℂ)⁻¹) •
        coefficient.1 (cell, zeroDerivativeIndexAt grade)
          (rotatedPoint (2 * Real.pi * time) point) =
    ((coefficientScale L sigma gamma ell grade cell
      (zeroDerivativeIndexAt grade)
        (rotatedPoint (2 * Real.pi * time) point) : ℂ)⁻¹) •
        coefficient.1 (cell, zeroDerivativeIndexAt grade)
          (rotatedPoint (2 * Real.pi * time) point)
  congr 2
  unfold coefficientScale originalEnvelope
  rw [show ‖(rotatedPoint (2 * Real.pi * time) point).val‖ = ‖point.val‖ by
    exact planeRotation_norm (2 * Real.pi * time) point.val]

end Grad.GaugeCoefficients.Radial
