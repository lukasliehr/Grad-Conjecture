import GC13Radial

noncomputable section

set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 200000

open Set MeasureTheory
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators ENNReal Interval Topology

namespace Grad.GaugeCoefficients.Radial

open Grad.GaugeCoefficients.Algebra

def radialWeightedDerivativeCurve
    (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ} (cell : ℤ)
    (field : SmoothOperatorJet inputDimension outputDimension)
    (index : DerivativeIndex grade) (time : ℝ) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  (Real.negMulLog time : ℂ) • weightedSmoothDerivative L sigma gamma ell grade cell
    (radialSmoothOperatorJet time field) index

theorem radialWeightedDerivativeCurve_apply
    (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ} (cell : ℤ)
    (field : SmoothOperatorJet inputDimension outputDimension)
    (index : DerivativeIndex grade) (time : ℝ) (point : ClosedDisk) :
    radialWeightedDerivativeCurve L sigma gamma ell grade cell field index time point =
      (Real.negMulLog time : ℂ) •
        ((coefficientScale L sigma gamma ell grade cell index point : ℂ) •
          ((unitClamp time ^ derivativeOrder index : ℝ) : ℂ) •
            smoothOperatorDerivative field (derivativeMultiIndex index)
              (radialPoint time point)) := by
  change (Real.negMulLog time : ℂ) •
    ((coefficientScale L sigma gamma ell grade cell index point : ℂ) •
      smoothOperatorDerivative (radialSmoothOperatorJet time field)
        (derivativeMultiIndex index) point) = _
  rw [radialSmoothOperatorJet_derivative_apply]
  rfl

theorem continuous_radialWeightedDerivativeCurve
    (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ} (cell : ℤ)
    (field : SmoothOperatorJet inputDimension outputDimension)
    (index : DerivativeIndex grade) :
    Continuous (radialWeightedDerivativeCurve L sigma gamma ell grade cell field index) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun pair : ℝ × ClosedDisk =>
    radialWeightedDerivativeCurve L sigma gamma ell grade cell field index pair.1 pair.2)
  simp_rw [radialWeightedDerivativeCurve_apply]
  exact (Complex.continuous_ofReal.comp
    (Real.continuous_negMulLog.comp continuous_fst)).smul
      ((Complex.continuous_ofReal.comp
        ((continuous_coefficientScale L sigma gamma ell grade cell index).comp
          continuous_snd)).smul
        ((Complex.continuous_ofReal.comp
          ((continuous_unitClamp.comp continuous_fst).pow _)).smul
          ((smoothOperatorDerivative field (derivativeMultiIndex index)).continuous.comp
            continuous_radialPoint_joint)))

def radialWeightedSingleCurve
    (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ} (cell : ℤ)
    (field : SmoothOperatorJet inputDimension outputDimension) :
    ℝ → WeightedAmbient grade inputDimension outputDimension :=
  fun time => (Real.negMulLog time : ℂ) •
    weightedSingle L sigma gamma ell grade cell (radialSmoothOperatorJet time field)

theorem continuous_radialWeightedSingleCurve
    (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ} (cell : ℤ)
    (field : SmoothOperatorJet inputDimension outputDimension) :
    Continuous (radialWeightedSingleCurve L sigma gamma ell grade cell field) := by
  have decomposition :
      radialWeightedSingleCurve L sigma gamma ell grade cell field =
        fun time => ∑ index : DerivativeIndex grade,
          (lp.singleContinuousLinearMap ℂ
            (fun _ : ℤ × DerivativeIndex grade =>
              ContinuousMap ClosedDisk
                (OperatorValue inputDimension outputDimension)) 1 (cell, index))
            (radialWeightedDerivativeCurve L sigma gamma ell grade cell field index time) := by
    funext time
    unfold radialWeightedSingleCurve weightedSingle
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro index _membership
    unfold radialWeightedDerivativeCurve
    rw [map_smul]
    rfl
  rw [decomposition]
  apply continuous_finsetSum
  intro index _membership
  exact (lp.singleContinuousLinearMap ℂ
      (fun _ : ℤ × DerivativeIndex grade =>
        ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension))
      1 (cell, index)).continuous.comp
    (continuous_radialWeightedDerivativeCurve L sigma gamma ell grade cell field index)

theorem rawRadialCoordinateJoint_weightedSingle
    (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ} (cell : ℤ)
    (field : SmoothOperatorJet inputDimension outputDimension)
    (other : ℤ) (index : DerivativeIndex grade) (time : ℝ) (point : ClosedDisk) :
    rawRadialCoordinateJoint (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
      (weightedSingle L sigma gamma ell grade cell field) other index (time, point) =
    radialWeightedSingleCurve L sigma gamma ell grade cell field time (other, index) point := by
  change (Real.negMulLog time : ℂ) •
      ((radialScaleRatio L sigma gamma ell grade other index time point *
        unitClamp time ^ derivativeOrder index : ℝ) : ℂ) •
        weightedSingle L sigma gamma ell grade cell field (other, index)
          (radialPoint time point) =
    (Real.negMulLog time : ℂ) •
      weightedSingle L sigma gamma ell grade cell (radialSmoothOperatorJet time field)
        (other, index) point
  by_cases same : other = cell
  · subst other
    rw [weightedSingle_apply_same, weightedSingle_apply_same]
    change (Real.negMulLog time : ℂ) •
      ((radialScaleRatio L sigma gamma ell grade cell index time point *
        unitClamp time ^ derivativeOrder index : ℝ) : ℂ) •
        ((coefficientScale L sigma gamma ell grade cell index
          (radialPoint time point) : ℂ) •
            smoothOperatorDerivative field (derivativeMultiIndex index)
              (radialPoint time point)) =
      (Real.negMulLog time : ℂ) •
        ((coefficientScale L sigma gamma ell grade cell index point : ℂ) •
          smoothOperatorDerivative (radialSmoothOperatorJet time field)
            (derivativeMultiIndex index) point)
    rw [radialSmoothOperatorJet_derivative_apply]
    change (Real.negMulLog time : ℂ) •
      ((radialScaleRatio L sigma gamma ell grade cell index time point *
        unitClamp time ^ derivativeOrder index : ℝ) : ℂ) •
        ((coefficientScale L sigma gamma ell grade cell index
          (radialPoint time point) : ℂ) •
            smoothOperatorDerivative field (derivativeMultiIndex index)
              (radialPoint time point)) =
      (Real.negMulLog time : ℂ) •
        ((coefficientScale L sigma gamma ell grade cell index point : ℂ) •
          ((unitClamp time ^ derivativeOrder index : ℝ) : ℂ) •
            smoothOperatorDerivative field (derivativeMultiIndex index)
              (radialPoint time point))
    have nonzero : (coefficientScale L sigma gamma ell grade cell index
        (radialPoint time point) : ℂ) ≠ 0 := by
      exact_mod_cast (coefficientScale_pos L sigma gamma ell grade cell index
        (radialPoint time point)).ne'
    congr 1
    simp only [smul_smul, radialScaleRatio, Complex.ofReal_mul, Complex.ofReal_div]
    congr 1
    field_simp
  · rw [weightedSingle_apply L sigma gamma ell grade cell other,
      weightedSingle_apply L sigma gamma ell grade cell other]
    simp only [same, if_false, ContinuousMap.zero_apply]
    apply ContinuousLinearMap.ext
    intro vector
    apply PiLp.ext
    intro coordinate
    change (Real.negMulLog time : ℂ) *
      (((radialScaleRatio L sigma gamma ell grade other index time point *
        unitClamp time ^ derivativeOrder index : ℝ) : ℂ) * 0) =
      (Real.negMulLog time : ℂ) * 0
    ring

theorem rawRadial_weightedSingle_mem_closure
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) {inputDimension outputDimension : ℕ} (cell : ℤ)
    (field : SmoothOperatorJet inputDimension outputDimension) :
    rawRadial admissible (weightedSingle L sigma gamma ell grade cell field) ∈
      (smoothCore L sigma gamma ell grade
        inputDimension outputDimension).topologicalClosure := by
  let core := smoothCore L sigma gamma ell grade inputDimension outputDimension
  let orbit := radialWeightedSingleCurve L sigma gamma ell grade cell field
  have orbitContinuous : Continuous orbit :=
    continuous_radialWeightedSingleCurve L sigma gamma ell grade cell field
  have orbitIntegrable : IntegrableOn orbit (Icc (0 : ℝ) 1) :=
    orbitContinuous.continuousOn.integrableOn_compact isCompact_Icc
  have orbitMembership (time : ℝ) : orbit time ∈ core := by
    exact core.smul_mem (Real.negMulLog time : ℂ)
      (Submodule.subset_span (Set.mem_range.mpr
        ⟨(cell, radialSmoothOperatorJet time field), rfl⟩))
  have integralMembership : (∫ time in Icc (0 : ℝ) 1, orbit time) ∈
      core.topologicalClosure := by
    let _ : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := by
      rw [isProbabilityMeasure_iff, Measure.restrict_apply_univ, Real.volume_Icc]
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
  suffices equality : rawRadial admissible
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
      rawRadialCoordinateJoint (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
        (weightedSingle L sigma gamma ell grade cell field)
          pair.1 pair.2 (time, point)) = pointEvaluation
            (∫ time in Icc (0 : ℝ) 1, orbit time)
  calc
    _ = ∫ time in Icc (0 : ℝ) 1, pointEvaluation (orbit time) := by
      apply integral_congr_ae
      filter_upwards with time
      exact rawRadialCoordinateJoint_weightedSingle L sigma gamma ell grade cell
        field pair.1 pair.2 time point
    _ = pointEvaluation (∫ time in Icc (0 : ℝ) 1, orbit time) :=
      ContinuousLinearMap.integral_comp_comm (𝕜 := ℂ)
        pointEvaluation orbitIntegrable

theorem rawRadial_smoothCore_mem_closure
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade inputDimension outputDimension : ℕ)
    (coefficient : smoothCore L sigma gamma ell grade
      inputDimension outputDimension) :
    rawRadial admissible coefficient.1 ∈
      (smoothCore L sigma gamma ell grade
        inputDimension outputDimension).topologicalClosure := by
  let core := smoothCore L sigma gamma ell grade inputDimension outputDimension
  refine Submodule.span_induction
    (p := fun value _membership => rawRadial admissible value ∈ core.topologicalClosure)
      ?generator ?zero ?add ?smul coefficient.2
  case generator =>
    intro generator membership
    rcases membership with ⟨pair, rfl⟩
    exact rawRadial_weightedSingle_mem_closure admissible grade pair.1 pair.2
  case zero =>
    change rawRadialLinear admissible grade inputDimension outputDimension 0 ∈
      core.topologicalClosure
    rw [map_zero]
    exact core.topologicalClosure.zero_mem
  case add =>
    intro first second _ _ firstMembership secondMembership
    change rawRadialLinear admissible grade inputDimension outputDimension
      (first + second) ∈ core.topologicalClosure
    rw [map_add]
    exact core.topologicalClosure.add_mem firstMembership secondMembership
  case smul =>
    intro scalar value _ valueMembership
    change rawRadialLinear admissible grade inputDimension outputDimension
      (scalar • value) ∈ core.topologicalClosure
    rw [map_smul]
    exact core.topologicalClosure.smul_mem scalar valueMembership

theorem rawRadial_closure
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade inputDimension outputDimension : ℕ)
    (coefficient : Coefficient L sigma gamma ell grade
      inputDimension outputDimension) :
    rawRadial admissible coefficient.1 ∈
      (smoothCore L sigma gamma ell grade
        inputDimension outputDimension).topologicalClosure := by
  let core := smoothCore L sigma gamma ell grade inputDimension outputDimension
  let operation := rawRadialMap admissible grade inputDimension outputDimension
  have coreMapLe : core.map (operation : _ →ₗ[ℂ] _) ≤
      core.topologicalClosure := by
    intro output membership
    rcases membership with ⟨input, inputMembership, rfl⟩
    exact rawRadial_smoothCore_mem_closure admissible grade
      inputDimension outputDimension ⟨input, inputMembership⟩
  have mapped : operation coefficient.1 ∈ core.topologicalClosure.map
      (operation : _ →ₗ[ℂ] _) := ⟨coefficient.1, coefficient.2, rfl⟩
  have twice : operation coefficient.1 ∈
      core.topologicalClosure.topologicalClosure :=
    (Submodule.topologicalClosure_mono coreMapLe)
      ((core.topologicalClosure_map operation) mapped)
  rw [core.isClosed_topologicalClosure.submodule_topologicalClosure_eq] at twice
  exact twice

def coefficientRadial
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade inputDimension outputDimension : ℕ)
    (coefficient : Coefficient L sigma gamma ell grade
      inputDimension outputDimension) :
    Coefficient L sigma gamma ell grade inputDimension outputDimension :=
  ⟨rawRadial admissible coefficient.1,
    rawRadial_closure admissible grade inputDimension outputDimension coefficient⟩

def coefficientRadialLinear
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade inputDimension outputDimension : ℕ) :
    Coefficient L sigma gamma ell grade inputDimension outputDimension →ₗ[ℂ]
      Coefficient L sigma gamma ell grade inputDimension outputDimension where
  toFun := coefficientRadial admissible grade inputDimension outputDimension
  map_add' first second := by
    apply Subtype.ext
    exact (rawRadialLinear admissible grade inputDimension outputDimension).map_add _ _
  map_smul' scalar coefficient := by
    apply Subtype.ext
    exact (rawRadialLinear admissible grade inputDimension outputDimension).map_smul _ _

def coefficientRadialMap
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade inputDimension outputDimension : ℕ) :
    Coefficient L sigma gamma ell grade inputDimension outputDimension →L[ℂ]
      Coefficient L sigma gamma ell grade inputDimension outputDimension :=
  (coefficientRadialLinear admissible grade inputDimension outputDimension).mkContinuous
    ((1 : ℝ) / 4) (fun coefficient => rawRadial_norm_le admissible coefficient.1)

theorem coefficientRadial_bound
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade inputDimension outputDimension : ℕ)
    (coefficient : Coefficient L sigma gamma ell grade
      inputDimension outputDimension) :
    ‖coefficientRadialMap admissible grade inputDimension outputDimension coefficient‖ ≤
      (1 : ℝ) / 4 * ‖coefficient‖ :=
  rawRadial_norm_le admissible coefficient.1

theorem coefficientRadial_derivative
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade inputDimension outputDimension : ℕ)
    (coefficient : Coefficient L sigma gamma ell grade
      inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative
        (coefficientRadialMap admissible grade inputDimension outputDimension coefficient)
        cell index point = radialIntegralDerivative coefficient cell index point := by
  unfold coefficientDerivative weightedDerivative radialIntegralDerivative
  change ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
      (∫ time in Icc (0 : ℝ) 1,
        rawRadialCoordinateJoint (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
          coefficient.1 cell index (time, point)) = _
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with time membership
  change ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
    ((Real.negMulLog time : ℂ) •
      ((radialScaleRatio L sigma gamma ell grade cell index time point *
        unitClamp time ^ derivativeOrder index : ℝ) : ℂ) •
          coefficient.1 (cell, index) (radialPoint time point)) =
    (Real.negMulLog time : ℂ) • ((time ^ derivativeOrder index : ℝ) : ℂ) •
      ((coefficientScale L sigma gamma ell grade cell index
        (radialPoint time point) : ℂ)⁻¹) •
          coefficient.1 (cell, index) (radialPoint time point)
  rw [unitClamp_of_mem membership]
  have nonzero : (coefficientScale L sigma gamma ell grade cell index point : ℂ) ≠ 0 := by
    exact_mod_cast (coefficientScale_pos L sigma gamma ell grade cell index point).ne'
  simp only [smul_smul, radialScaleRatio, Complex.ofReal_mul, Complex.ofReal_div]
  congr 1
  field_simp

end Grad.GaugeCoefficients.Radial
