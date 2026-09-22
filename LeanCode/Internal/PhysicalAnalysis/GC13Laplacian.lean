import GC13Smooth

noncomputable section

set_option maxHeartbeats 5000000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators ENNReal Topology

namespace Grad.GaugeCoefficients.Radial

open Grad.GaugeCoefficients.Algebra

theorem coefficientScale_firstLaplacian
    (L sigma gamma ell : ℝ) (grade : ℕ) (cell : ℤ)
    (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientScale L sigma gamma ell (grade + 2) cell
        (firstLaplacianIndex index) point =
      coefficientScale L sigma gamma ell grade cell index point := by
  have orderEquality : derivativeOrder (firstLaplacianIndex index) =
      derivativeOrder index + 2 := by
    change (index.1.1 : ℕ) + 2 + (index.1.2 : ℕ) =
      ((index.1.1 : ℕ) + (index.1.2 : ℕ)) + 2
    omega
  have orderLe : derivativeOrder index ≤ grade := index.2
  have exponentEquality :
      grade + 2 - (derivativeOrder index + 2) = grade - derivativeOrder index := by
    omega
  unfold coefficientScale
  rw [orderEquality, exponentEquality]

theorem coefficientScale_secondLaplacian
    (L sigma gamma ell : ℝ) (grade : ℕ) (cell : ℤ)
    (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientScale L sigma gamma ell (grade + 2) cell
        (secondLaplacianIndex index) point =
      coefficientScale L sigma gamma ell grade cell index point := by
  have orderEquality : derivativeOrder (secondLaplacianIndex index) =
      derivativeOrder index + 2 := by
    change (index.1.1 : ℕ) + ((index.1.2 : ℕ) + 2) =
      ((index.1.1 : ℕ) + (index.1.2 : ℕ)) + 2
    omega
  have orderLe : derivativeOrder index ≤ grade := index.2
  have exponentEquality :
      grade + 2 - (derivativeOrder index + 2) = grade - derivativeOrder index := by
    omega
  unfold coefficientScale
  rw [orderEquality, exponentEquality]

def rawLaplacian {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient (grade + 2) inputDimension outputDimension) :
    WeightedAmbient grade inputDimension outputDimension := by
  refine ⟨fun pair =>
    coefficient (pair.1, firstLaplacianIndex pair.2) +
      coefficient (pair.1, secondLaplacianIndex pair.2), ?_⟩
  apply memℓp_gen
  have each (index : DerivativeIndex grade) : Summable (fun cell : ℤ =>
      ‖coefficient (cell, firstLaplacianIndex index) +
        coefficient (cell, secondLaplacianIndex index)‖) :=
    Summable.of_nonneg_of_le
      (fun cell => norm_nonneg
        (coefficient (cell, firstLaplacianIndex index) +
          coefficient (cell, secondLaplacianIndex index)))
      (fun cell => norm_add_le
        (coefficient (cell, firstLaplacianIndex index) :
          ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension))
        (coefficient (cell, secondLaplacianIndex index) :
          ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension)))
      ((coordinate_norm_summable coefficient (firstLaplacianIndex index)).add
        (coordinate_norm_summable coefficient (secondLaplacianIndex index)))
  have swapped : Summable (fun pair : DerivativeIndex grade × ℤ =>
      ‖coefficient (pair.2, firstLaplacianIndex pair.1) +
        coefficient (pair.2, secondLaplacianIndex pair.1)‖) := by
    apply (summable_prod_of_nonneg (fun pair => norm_nonneg
      (coefficient (pair.2, firstLaplacianIndex pair.1) +
        coefficient (pair.2, secondLaplacianIndex pair.1)))).2
    exact ⟨each, (hasSum_fintype _).summable⟩
  have all : Summable (fun pair : ℤ × DerivativeIndex grade =>
      ‖coefficient (pair.1, firstLaplacianIndex pair.2) +
        coefficient (pair.1, secondLaplacianIndex pair.2)‖) := by
    apply (Equiv.prodComm (DerivativeIndex grade) ℤ).summable_iff.mp
    change Summable (fun pair : DerivativeIndex grade × ℤ =>
      ‖coefficient (pair.2, firstLaplacianIndex pair.1) +
        coefficient (pair.2, secondLaplacianIndex pair.1)‖)
    exact swapped
  have oneToReal : (1 : ℝ≥0∞).toReal = 1 := by norm_num
  simpa only [oneToReal, Real.rpow_one] using all

@[simp] theorem rawLaplacian_apply {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient (grade + 2) inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    rawLaplacian coefficient (cell, index) =
      coefficient (cell, firstLaplacianIndex index) +
        coefficient (cell, secondLaplacianIndex index) := rfl

theorem rawLaplacian_norm_le {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient (grade + 2) inputDimension outputDimension) :
    ‖rawLaplacian coefficient‖ ≤ laplacianBound grade * ‖coefficient‖ := by
  rw [ambient_norm_formula]
  calc
    (∑ index : DerivativeIndex grade, ∑' cell : ℤ,
        ‖rawLaplacian coefficient (cell, index)‖)
        ≤ ∑ index : DerivativeIndex grade,
          ((∑' cell : ℤ, ‖coefficient (cell, firstLaplacianIndex index)‖) +
            ∑' cell : ℤ, ‖coefficient (cell, secondLaplacianIndex index)‖) := by
      apply Finset.sum_le_sum
      intro index _membership
      calc
        (∑' cell : ℤ, ‖rawLaplacian coefficient (cell, index)‖) ≤
            ∑' cell : ℤ,
              (‖coefficient (cell, firstLaplacianIndex index)‖ +
                ‖coefficient (cell, secondLaplacianIndex index)‖) :=
          Summable.tsum_le_tsum (fun cell => norm_add_le
            (coefficient (cell, firstLaplacianIndex index) :
              ContinuousMap ClosedDisk
                (OperatorValue inputDimension outputDimension))
            (coefficient (cell, secondLaplacianIndex index) :
              ContinuousMap ClosedDisk
                (OperatorValue inputDimension outputDimension)))
            (coordinate_norm_summable (rawLaplacian coefficient) index)
            ((coordinate_norm_summable coefficient (firstLaplacianIndex index)).add
              (coordinate_norm_summable coefficient (secondLaplacianIndex index)))
        _ = _ := (coordinate_norm_summable coefficient
            (firstLaplacianIndex index)).tsum_add
          (coordinate_norm_summable coefficient (secondLaplacianIndex index))
    _ ≤ ∑ _index : DerivativeIndex grade, (‖coefficient‖ + ‖coefficient‖) := by
      apply Finset.sum_le_sum
      intro index _membership
      exact add_le_add
        (coordinate_norm_sum_le coefficient (firstLaplacianIndex index))
        (coordinate_norm_sum_le coefficient (secondLaplacianIndex index))
    _ = laplacianBound grade * ‖coefficient‖ := by
      simp [laplacianBound]
      ring

def rawLaplacianLinear (grade inputDimension outputDimension : ℕ) :
    WeightedAmbient (grade + 2) inputDimension outputDimension →ₗ[ℂ]
      WeightedAmbient grade inputDimension outputDimension where
  toFun := rawLaplacian
  map_add' first second := by
    apply lp.ext
    funext pair
    change (first (pair.1, firstLaplacianIndex pair.2) +
        second (pair.1, firstLaplacianIndex pair.2)) +
      (first (pair.1, secondLaplacianIndex pair.2) +
        second (pair.1, secondLaplacianIndex pair.2)) =
      (first (pair.1, firstLaplacianIndex pair.2) +
        first (pair.1, secondLaplacianIndex pair.2)) +
      (second (pair.1, firstLaplacianIndex pair.2) +
        second (pair.1, secondLaplacianIndex pair.2))
    abel
  map_smul' scalar coefficient := by
    apply lp.ext
    funext pair
    change scalar • coefficient (pair.1, firstLaplacianIndex pair.2) +
        scalar • coefficient (pair.1, secondLaplacianIndex pair.2) =
      scalar • (coefficient (pair.1, firstLaplacianIndex pair.2) +
        coefficient (pair.1, secondLaplacianIndex pair.2))
    exact (smul_add scalar _ _).symm

def rawLaplacianMap (grade inputDimension outputDimension : ℕ) :
    WeightedAmbient (grade + 2) inputDimension outputDimension →L[ℂ]
      WeightedAmbient grade inputDimension outputDimension :=
  (rawLaplacianLinear grade inputDimension outputDimension).mkContinuous
    (laplacianBound grade) rawLaplacian_norm_le

theorem rawLaplacian_weightedSingle
    (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ} (cell : ℤ)
    (field : SmoothOperatorJet inputDimension outputDimension) :
    rawLaplacian (weightedSingle L sigma gamma ell (grade + 2) cell field) =
      weightedSingle L sigma gamma ell grade cell
        (laplacianSmoothOperatorJet field) := by
  apply lp.ext
  funext pair
  rcases pair with ⟨other, index⟩
  rw [rawLaplacian_apply]
  by_cases same : other = cell
  · subst other
    rw [weightedSingle_apply_same, weightedSingle_apply_same,
      weightedSingle_apply_same]
    apply ContinuousMap.ext
    intro point
    change
      (coefficientScale L sigma gamma ell (grade + 2) cell
          (firstLaplacianIndex index) point : ℂ) •
          smoothOperatorDerivative field
            (derivativeMultiIndex (firstLaplacianIndex index)) point +
        (coefficientScale L sigma gamma ell (grade + 2) cell
          (secondLaplacianIndex index) point : ℂ) •
          smoothOperatorDerivative field
            (derivativeMultiIndex (secondLaplacianIndex index)) point =
        (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
          smoothOperatorDerivative (laplacianSmoothOperatorJet field)
            (derivativeMultiIndex index) point
    rw [coefficientScale_firstLaplacian,
      coefficientScale_secondLaplacian,
      laplacianSmoothOperatorJet_derivative]
    change
      (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
          smoothOperatorDerivative field
            (derivativeMultiIndex (firstLaplacianIndex index)) point +
        (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
          smoothOperatorDerivative field
            (derivativeMultiIndex (secondLaplacianIndex index)) point =
      (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
        (smoothOperatorDerivative field
            ((derivativeMultiIndex index).1 + 2, (derivativeMultiIndex index).2) point +
          smoothOperatorDerivative field
            ((derivativeMultiIndex index).1, (derivativeMultiIndex index).2 + 2) point)
    rw [smul_add]
    rfl
  · rw [weightedSingle_apply L sigma gamma ell (grade + 2) cell other,
      weightedSingle_apply L sigma gamma ell (grade + 2) cell other,
      weightedSingle_apply L sigma gamma ell grade cell other]
    simp [same]

theorem rawLaplacian_mem_smoothCore
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (coefficient : smoothCore L sigma gamma ell (grade + 2)
      inputDimension outputDimension) :
    rawLaplacian coefficient.1 ∈
      smoothCore L sigma gamma ell grade inputDimension outputDimension := by
  let target := smoothCore L sigma gamma ell grade inputDimension outputDimension
  refine Submodule.span_induction
    (p := fun value _membership => rawLaplacian value ∈ target) ?generator
      ?zero ?add ?smul coefficient.2
  case generator =>
    intro generator membership
    rcases membership with ⟨pair, rfl⟩
    rw [rawLaplacian_weightedSingle]
    exact Submodule.subset_span
      (Set.mem_range.mpr ⟨(pair.1, laplacianSmoothOperatorJet pair.2), rfl⟩)
  case zero =>
    change rawLaplacianLinear grade inputDimension outputDimension 0 ∈ target
    rw [map_zero]
    exact target.zero_mem
  case add =>
    intro first second _ _ firstMembership secondMembership
    change rawLaplacianLinear grade inputDimension outputDimension (first + second) ∈ target
    rw [map_add]
    exact target.add_mem firstMembership secondMembership
  case smul =>
    intro scalar value _ valueMembership
    change rawLaplacianLinear grade inputDimension outputDimension (scalar • value) ∈ target
    rw [map_smul]
    exact target.smul_mem scalar valueMembership

theorem rawLaplacian_closure
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (coefficient : Coefficient L sigma gamma ell (grade + 2)
      inputDimension outputDimension) :
    rawLaplacian coefficient.1 ∈
      (smoothCore L sigma gamma ell grade inputDimension outputDimension).topologicalClosure := by
  let source := smoothCore L sigma gamma ell (grade + 2)
    inputDimension outputDimension
  let target := smoothCore L sigma gamma ell grade inputDimension outputDimension
  let operation := rawLaplacianMap grade inputDimension outputDimension
  have sourceMapLe : source.map (operation : _ →ₗ[ℂ] _) ≤ target := by
    intro output membership
    rcases membership with ⟨input, inputMembership, rfl⟩
    exact rawLaplacian_mem_smoothCore L sigma gamma ell grade inputDimension
      outputDimension ⟨input, inputMembership⟩
  have mapped : operation coefficient.1 ∈ source.topologicalClosure.map
      (operation : _ →ₗ[ℂ] _) := ⟨coefficient.1, coefficient.2, rfl⟩
  exact (Submodule.topologicalClosure_mono sourceMapLe)
    ((source.topologicalClosure_map operation) mapped)

def coefficientLaplacian
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (coefficient : Coefficient L sigma gamma ell (grade + 2)
      inputDimension outputDimension) :
    Coefficient L sigma gamma ell grade inputDimension outputDimension :=
  ⟨rawLaplacian coefficient.1,
    rawLaplacian_closure L sigma gamma ell grade inputDimension outputDimension coefficient⟩

def coefficientLaplacianLinear
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ) :
    Coefficient L sigma gamma ell (grade + 2) inputDimension outputDimension →ₗ[ℂ]
      Coefficient L sigma gamma ell grade inputDimension outputDimension where
  toFun := coefficientLaplacian L sigma gamma ell grade inputDimension outputDimension
  map_add' first second := by
    apply Subtype.ext
    exact (rawLaplacianLinear grade inputDimension outputDimension).map_add _ _
  map_smul' scalar coefficient := by
    apply Subtype.ext
    exact (rawLaplacianLinear grade inputDimension outputDimension).map_smul _ _

def coefficientLaplacianMap
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ) :
    Coefficient L sigma gamma ell (grade + 2) inputDimension outputDimension →L[ℂ]
      Coefficient L sigma gamma ell grade inputDimension outputDimension :=
  (coefficientLaplacianLinear L sigma gamma ell grade inputDimension
    outputDimension).mkContinuous (laplacianBound grade)
      (fun coefficient => rawLaplacian_norm_le coefficient.1)

theorem coefficientLaplacian_bound
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (coefficient : Coefficient L sigma gamma ell (grade + 2)
      inputDimension outputDimension) :
    ‖coefficientLaplacianMap L sigma gamma ell grade inputDimension
      outputDimension coefficient‖ ≤ laplacianBound grade * ‖coefficient‖ :=
  rawLaplacian_norm_le coefficient.1

theorem coefficientLaplacian_derivative
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (coefficient : Coefficient L sigma gamma ell (grade + 2)
      inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative
        (coefficientLaplacianMap L sigma gamma ell grade inputDimension
          outputDimension coefficient) cell index point =
      laplacianDerivative coefficient cell index point := by
  change ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
      (coefficient.1 (cell, firstLaplacianIndex index) +
        coefficient.1 (cell, secondLaplacianIndex index)) point = _
  change
    ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
      (coefficient.1 (cell, firstLaplacianIndex index) point +
        coefficient.1 (cell, secondLaplacianIndex index) point) =
    ((coefficientScale L sigma gamma ell (grade + 2) cell
      (firstLaplacianIndex index) point : ℂ)⁻¹) •
        coefficient.1 (cell, firstLaplacianIndex index) point +
      ((coefficientScale L sigma gamma ell (grade + 2) cell
        (secondLaplacianIndex index) point : ℂ)⁻¹) •
        coefficient.1 (cell, secondLaplacianIndex index) point
  rw [smul_add]
  rw [coefficientScale_firstLaplacian,
    coefficientScale_secondLaplacian]

end Grad.GaugeCoefficients.Radial
