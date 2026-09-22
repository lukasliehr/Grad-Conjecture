import GC13OrthogonalSmooth
import GC13Laplacian

noncomputable section

set_option maxHeartbeats 5000000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open Grad.RepresentedKernel.SpatialProduct
open scoped BigOperators ENNReal Topology

namespace Grad.GaugeCoefficients.Radial

open Grad.GaugeCoefficients.Algebra

theorem spatialDirection_norm (direction : Fin 2) :
    ‖spatialDirection direction‖ = 1 := by
  simp [spatialDirection, PiLp.norm_single]

theorem orthogonal_entry_bound
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (direction coordinate : Fin 2) :
    |orthogonal (spatialDirection direction) coordinate| ≤ 1 := by
  calc
    _ ≤ ‖orthogonal (spatialDirection direction)‖ := PiLp.norm_apply_le _ _
    _ = ‖spatialDirection direction‖ := orthogonal.norm_map _
    _ = 1 := spatialDirection_norm direction

theorem chainFactor_abs_le_one (rank : ℕ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (word target : Word rank) :
    |chainFactor rank orthogonal word target| ≤ 1 := by
  rw [chainFactor_eq, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
    (fun position _ => orthogonal_entry_bound orthogonal _ _)

def orthogonalClosedMap
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) :
    C(ClosedDisk, ClosedDisk) :=
  ⟨orthogonalClosedPoint orthogonal, continuous_orthogonalClosedPoint orthogonal⟩

theorem continuousMap_sum_apply {Domain Index Value : Type*}
    [TopologicalSpace Domain] [Fintype Index]
    [TopologicalSpace Value] [AddCommMonoid Value]
    [ContinuousAdd Value]
    (functions : Index → ContinuousMap Domain Value) (point : Domain) :
    (∑ index, functions index) point = ∑ index, functions index point := by
  let evaluation : ContinuousMap Domain Value →+ Value :=
    { toFun := fun function => function point
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change evaluation (∑ index, functions index) = ∑ index, evaluation (functions index)
  rw [map_sum]

theorem coefficientScale_orthogonal
    (L sigma gamma ell : ℝ) (grade : ℕ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (cell : ℤ) (index : DerivativeIndex grade)
    (target : Word (derivativeOrder index)) (point : ClosedDisk) :
    coefficientScale L sigma gamma ell grade cell
        (orthogonalDerivativeIndex index target)
        (orthogonalClosedPoint orthogonal point) =
      coefficientScale L sigma gamma ell grade cell index point := by
  have total := count_total (derivativeOrder index) target
  have orderEquality : derivativeOrder (orthogonalDerivativeIndex index target) =
      derivativeOrder index := by
    unfold derivativeOrder orthogonalDerivativeIndex
    change Grad.WeakTesting.Commutation.directionCount target 0 +
      Grad.WeakTesting.Commutation.directionCount target 1 = derivativeOrder index
    exact total
  unfold coefficientScale originalEnvelope
  have normEquality :
      ‖(orthogonalClosedPoint orthogonal point).val‖ = ‖point.val‖ :=
    orthogonal.norm_map point.val
  rw [normEquality, orderEquality]

def rawOrthogonalTerm {grade inputDimension outputDimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade)
    (target : Word (derivativeOrder index)) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  (chainFactor (derivativeOrder index) orthogonal
    (derivativeWord index) target : ℂ) •
      (coefficient (cell, orthogonalDerivativeIndex index target)).comp
        (orthogonalClosedMap orthogonal)

theorem rawOrthogonalTerm_norm_le {grade inputDimension outputDimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade)
    (target : Word (derivativeOrder index)) :
    ‖rawOrthogonalTerm orthogonal coefficient cell index target‖ ≤
      ‖coefficient (cell, orthogonalDerivativeIndex index target)‖ := by
  apply (ContinuousMap.norm_le _
    (norm_nonneg (coefficient
      (cell, orthogonalDerivativeIndex index target)))).2
  intro point
  change ‖(chainFactor (derivativeOrder index) orthogonal
      (derivativeWord index) target : ℂ) •
        coefficient (cell, orthogonalDerivativeIndex index target)
          (orthogonalClosedPoint orthogonal point)‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ 1 * ‖coefficient (cell, orthogonalDerivativeIndex index target)‖ := by
      apply mul_le_mul (chainFactor_abs_le_one _ orthogonal _ target)
        (ContinuousMap.norm_coe_le_norm _ (orthogonalClosedPoint orthogonal point))
        (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

def rawOrthogonalCoordinate {grade inputDimension outputDimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  ∑ target : Word (derivativeOrder index),
    rawOrthogonalTerm orthogonal coefficient cell index target

theorem rawOrthogonalCoordinate_norm_le
    {grade inputDimension outputDimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    ‖rawOrthogonalCoordinate orthogonal coefficient cell index‖ ≤
      ∑ target : Word (derivativeOrder index),
        ‖coefficient (cell, orthogonalDerivativeIndex index target)‖ := by
  refine (ContinuousMap.norm_le
    (rawOrthogonalCoordinate orthogonal coefficient cell index)
    (Finset.sum_nonneg fun target _ => norm_nonneg
      (coefficient (cell, orthogonalDerivativeIndex index target)))).2 ?_
  intro point
  change ‖(∑ target : Word (derivativeOrder index),
      rawOrthogonalTerm orthogonal coefficient cell index target) point‖ ≤ _
  rw [continuousMap_sum_apply]
  calc
    ‖∑ target : Word (derivativeOrder index),
        rawOrthogonalTerm orthogonal coefficient cell index target point‖ ≤
      ∑ target : Word (derivativeOrder index),
        ‖rawOrthogonalTerm orthogonal coefficient cell index target point‖ :=
      norm_sum_le _ _
    _ ≤ ∑ target : Word (derivativeOrder index),
        ‖rawOrthogonalTerm orthogonal coefficient cell index target‖ :=
      Finset.sum_le_sum fun target _ => ContinuousMap.norm_coe_le_norm _ point
    _ ≤ _ := Finset.sum_le_sum fun target _ =>
      rawOrthogonalTerm_norm_le orthogonal coefficient cell index target

def rawOrthogonal
    {grade inputDimension outputDimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (coefficient : WeightedAmbient grade inputDimension outputDimension) :
    WeightedAmbient grade inputDimension outputDimension := by
  refine ⟨fun pair => rawOrthogonalCoordinate orthogonal coefficient pair.1 pair.2, ?_⟩
  apply memℓp_gen
  have each (index : DerivativeIndex grade) : Summable (fun cell : ℤ =>
      ‖rawOrthogonalCoordinate orthogonal coefficient cell index‖) :=
    Summable.of_nonneg_of_le
      (fun cell : ℤ => norm_nonneg
        (rawOrthogonalCoordinate orthogonal coefficient cell index))
      (fun cell => rawOrthogonalCoordinate_norm_le orthogonal coefficient cell index)
      (hasSum_sum (fun target _ => (coordinate_norm_summable coefficient
        (orthogonalDerivativeIndex index target)).hasSum)).summable
  have swapped : Summable (fun pair : DerivativeIndex grade × ℤ =>
      ‖rawOrthogonalCoordinate orthogonal coefficient pair.2 pair.1‖) := by
    apply (summable_prod_of_nonneg (fun pair : DerivativeIndex grade × ℤ =>
      norm_nonneg
        (rawOrthogonalCoordinate orthogonal coefficient pair.2 pair.1))).2
    exact ⟨each, (hasSum_fintype _).summable⟩
  have all : Summable (fun pair : ℤ × DerivativeIndex grade =>
      ‖rawOrthogonalCoordinate orthogonal coefficient pair.1 pair.2‖) := by
    apply (Equiv.prodComm (DerivativeIndex grade) ℤ).summable_iff.mp
    exact swapped
  have oneToReal : (1 : ℝ≥0∞).toReal = 1 := by norm_num
  simpa only [oneToReal, Real.rpow_one] using all

@[simp] theorem rawOrthogonal_apply
    {grade inputDimension outputDimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    rawOrthogonal orthogonal coefficient (cell, index) =
      rawOrthogonalCoordinate orthogonal coefficient cell index := rfl

theorem rawOrthogonal_norm_le
    {grade inputDimension outputDimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (coefficient : WeightedAmbient grade inputDimension outputDimension) :
    ‖rawOrthogonal orthogonal coefficient‖ ≤ angularBound grade * ‖coefficient‖ := by
  rw [ambient_norm_formula]
  calc
    (∑ index : DerivativeIndex grade, ∑' cell : ℤ,
      ‖rawOrthogonal orthogonal coefficient (cell, index)‖) ≤
        ∑ index : DerivativeIndex grade,
          ∑ target : Word (derivativeOrder index), ‖coefficient‖ := by
      apply Finset.sum_le_sum
      intro index _membership
      calc
        (∑' cell : ℤ, ‖rawOrthogonal orthogonal coefficient (cell, index)‖) ≤
            ∑' cell : ℤ, ∑ target : Word (derivativeOrder index),
              ‖coefficient (cell, orthogonalDerivativeIndex index target)‖ :=
          Summable.tsum_le_tsum
            (fun cell => rawOrthogonalCoordinate_norm_le
              orthogonal coefficient cell index)
            (coordinate_norm_summable (rawOrthogonal orthogonal coefficient) index)
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
        Fintype.card_fin]
      simp only [nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg coefficient)
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) index.2
    _ = angularBound grade * ‖coefficient‖ := by
      simp [angularBound]
      ring

def rawOrthogonalLinear (grade inputDimension outputDimension : ℕ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) :
    WeightedAmbient grade inputDimension outputDimension →ₗ[ℂ]
      WeightedAmbient grade inputDimension outputDimension where
  toFun := rawOrthogonal orthogonal
  map_add' first second := by
    apply lp.ext
    funext pair
    change rawOrthogonalCoordinate orthogonal (first + second) pair.1 pair.2 =
      rawOrthogonalCoordinate orthogonal first pair.1 pair.2 +
        rawOrthogonalCoordinate orthogonal second pair.1 pair.2
    unfold rawOrthogonalCoordinate rawOrthogonalTerm
    simp only [lp.coeFn_add, Pi.add_apply, ContinuousMap.add_comp, smul_add,
      Finset.sum_add_distrib]
  map_smul' scalar coefficient := by
    apply lp.ext
    funext pair
    change rawOrthogonalCoordinate orthogonal (scalar • coefficient)
        pair.1 pair.2 =
      scalar • rawOrthogonalCoordinate orthogonal coefficient pair.1 pair.2
    unfold rawOrthogonalCoordinate rawOrthogonalTerm
    simp only [lp.coeFn_smul, Pi.smul_apply, ContinuousMap.smul_comp, smul_smul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro target _membership
    rw [smul_smul, mul_comm]

def rawOrthogonalMap (grade inputDimension outputDimension : ℕ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) :
    WeightedAmbient grade inputDimension outputDimension →L[ℂ]
      WeightedAmbient grade inputDimension outputDimension :=
  (rawOrthogonalLinear grade inputDimension outputDimension orthogonal).mkContinuous
    (angularBound grade) (rawOrthogonal_norm_le orthogonal)

theorem rawOrthogonal_weightedSingle
    (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (cell : ℤ) (field : SmoothOperatorJet inputDimension outputDimension) :
    rawOrthogonal orthogonal (weightedSingle L sigma gamma ell grade cell field) =
      weightedSingle L sigma gamma ell grade cell
        (orthogonalSmoothOperatorJet orthogonal field) := by
  apply lp.ext
  funext pair
  rcases pair with ⟨other, index⟩
  rw [rawOrthogonal_apply]
  by_cases same : other = cell
  · subst other
    rw [weightedSingle_apply_same]
    apply ContinuousMap.ext
    intro point
    change (∑ target : Word (derivativeOrder index),
      rawOrthogonalTerm orthogonal
        (weightedSingle L sigma gamma ell grade cell field) cell index target) point =
      (weightedSmoothDerivative L sigma gamma ell grade cell
        (orthogonalSmoothOperatorJet orthogonal field) index) point
    rw [continuousMap_sum_apply]
    change (∑ target : Word (derivativeOrder index),
      rawOrthogonalTerm orthogonal
        (weightedSingle L sigma gamma ell grade cell field) cell index target point) =
      (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
        smoothOperatorDerivative (orthogonalSmoothOperatorJet orthogonal field)
          (derivativeMultiIndex index) point
    rw [orthogonalSmoothOperatorJet_derivative_index_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro target _membership
    unfold rawOrthogonalTerm
    rw [weightedSingle_apply_same]
    change _ =
      (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
        ((chainFactor (derivativeOrder index) orthogonal
          (derivativeWord index) target : ℂ) •
          smoothOperatorDerivative field (orthogonalTargetIndex target)
            (orthogonalClosedPoint orthogonal point))
    change
      (chainFactor (derivativeOrder index) orthogonal
        (derivativeWord index) target : ℂ) •
        ((coefficientScale L sigma gamma ell grade cell
          (orthogonalDerivativeIndex index target)
          (orthogonalClosedPoint orthogonal point) : ℂ) •
          smoothOperatorDerivative field (orthogonalTargetIndex target)
            (orthogonalClosedPoint orthogonal point)) = _
    rw [coefficientScale_orthogonal]
    simp only [smul_smul]
    rw [mul_comm]
  · unfold rawOrthogonalCoordinate
    rw [weightedSingle_apply L sigma gamma ell grade cell other]
    simp only [same, if_false]
    apply Finset.sum_eq_zero
    intro target _membership
    unfold rawOrthogonalTerm
    rw [weightedSingle_apply L sigma gamma ell grade cell other]
    simp only [same, if_false, ContinuousMap.zero_comp]
    apply ContinuousMap.ext
    intro point
    change (chainFactor (derivativeOrder index) orthogonal
        (derivativeWord index) target : ℂ) •
          (0 : OperatorValue inputDimension outputDimension) =
      (0 : OperatorValue inputDimension outputDimension)
    apply ContinuousLinearMap.ext
    intro vector
    change (chainFactor (derivativeOrder index) orthogonal
        (derivativeWord index) target : ℂ) •
          (0 : PhysicalValue outputDimension) =
      (0 : PhysicalValue outputDimension)
    apply PiLp.ext
    intro coordinate
    change (chainFactor (derivativeOrder index) orthogonal
        (derivativeWord index) target : ℂ) * 0 = 0
    ring

theorem rawOrthogonal_mem_smoothCore
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (coefficient : smoothCore L sigma gamma ell grade
      inputDimension outputDimension) :
    rawOrthogonal orthogonal coefficient.1 ∈
      smoothCore L sigma gamma ell grade inputDimension outputDimension := by
  let target := smoothCore L sigma gamma ell grade inputDimension outputDimension
  refine Submodule.span_induction
    (p := fun value _membership => rawOrthogonal orthogonal value ∈ target)
      ?generator ?zero ?add ?smul coefficient.2
  case generator =>
    intro generator membership
    rcases membership with ⟨pair, rfl⟩
    rw [rawOrthogonal_weightedSingle]
    exact Submodule.subset_span (Set.mem_range.mpr
      ⟨(pair.1, orthogonalSmoothOperatorJet orthogonal pair.2), rfl⟩)
  case zero =>
    change rawOrthogonalLinear grade inputDimension outputDimension orthogonal 0 ∈ target
    rw [map_zero]
    exact target.zero_mem
  case add =>
    intro first second _ _ firstMembership secondMembership
    change rawOrthogonalLinear grade inputDimension outputDimension orthogonal
      (first + second) ∈ target
    rw [map_add]
    exact target.add_mem firstMembership secondMembership
  case smul =>
    intro scalar value _ valueMembership
    change rawOrthogonalLinear grade inputDimension outputDimension orthogonal
      (scalar • value) ∈ target
    rw [map_smul]
    exact target.smul_mem scalar valueMembership

theorem rawOrthogonal_closure
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (coefficient : Coefficient L sigma gamma ell grade
      inputDimension outputDimension) :
    rawOrthogonal orthogonal coefficient.1 ∈
      (smoothCore L sigma gamma ell grade inputDimension outputDimension).topologicalClosure := by
  let core := smoothCore L sigma gamma ell grade inputDimension outputDimension
  let operation := rawOrthogonalMap grade inputDimension outputDimension orthogonal
  have coreMapLe : core.map (operation : _ →ₗ[ℂ] _) ≤ core := by
    intro output membership
    rcases membership with ⟨input, inputMembership, rfl⟩
    exact rawOrthogonal_mem_smoothCore L sigma gamma ell grade inputDimension
      outputDimension orthogonal ⟨input, inputMembership⟩
  have mapped : operation coefficient.1 ∈ core.topologicalClosure.map
      (operation : _ →ₗ[ℂ] _) := ⟨coefficient.1, coefficient.2, rfl⟩
  exact (Submodule.topologicalClosure_mono coreMapLe)
    ((core.topologicalClosure_map operation) mapped)

def coefficientOrthogonal
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (coefficient : Coefficient L sigma gamma ell grade
      inputDimension outputDimension) :
    Coefficient L sigma gamma ell grade inputDimension outputDimension :=
  ⟨rawOrthogonal orthogonal coefficient.1,
    rawOrthogonal_closure L sigma gamma ell grade inputDimension outputDimension
      orthogonal coefficient⟩

def coefficientOrthogonalLinear
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) :
    Coefficient L sigma gamma ell grade inputDimension outputDimension →ₗ[ℂ]
      Coefficient L sigma gamma ell grade inputDimension outputDimension where
  toFun := coefficientOrthogonal L sigma gamma ell grade inputDimension
    outputDimension orthogonal
  map_add' first second := by
    apply Subtype.ext
    exact (rawOrthogonalLinear grade inputDimension outputDimension orthogonal).map_add _ _
  map_smul' scalar coefficient := by
    apply Subtype.ext
    exact (rawOrthogonalLinear grade inputDimension outputDimension orthogonal).map_smul _ _

def coefficientOrthogonalMap
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) :
    Coefficient L sigma gamma ell grade inputDimension outputDimension →L[ℂ]
      Coefficient L sigma gamma ell grade inputDimension outputDimension :=
  (coefficientOrthogonalLinear L sigma gamma ell grade inputDimension
    outputDimension orthogonal).mkContinuous (angularBound grade)
      (fun coefficient => rawOrthogonal_norm_le orthogonal coefficient.1)

theorem coefficientOrthogonal_bound
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (coefficient : Coefficient L sigma gamma ell grade
      inputDimension outputDimension) :
    ‖coefficientOrthogonalMap L sigma gamma ell grade inputDimension
      outputDimension orthogonal coefficient‖ ≤
        angularBound grade * ‖coefficient‖ :=
  rawOrthogonal_norm_le orthogonal coefficient.1

theorem coefficientOrthogonal_derivative
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (coefficient : Coefficient L sigma gamma ell grade
      inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative
        (coefficientOrthogonalMap L sigma gamma ell grade inputDimension
          outputDimension orthogonal coefficient) cell index point =
      ∑ target : Word (derivativeOrder index),
        (chainFactor (derivativeOrder index) orthogonal
          (derivativeWord index) target : ℂ) •
        coefficientDerivative coefficient cell
          (orthogonalDerivativeIndex index target)
          (orthogonalClosedPoint orthogonal point) := by
  change ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
      (∑ target : Word (derivativeOrder index),
        rawOrthogonalTerm orthogonal coefficient.1 cell index target) point = _
  rw [continuousMap_sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro target _membership
  simp only [rawOrthogonalTerm, ContinuousMap.smul_apply, ContinuousMap.comp_apply]
  unfold coefficientDerivative weightedDerivative
  change
    ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
        ((chainFactor (derivativeOrder index) orthogonal
          (derivativeWord index) target : ℂ) •
          coefficient.1 (cell, orthogonalDerivativeIndex index target)
            (orthogonalClosedPoint orthogonal point)) =
      (chainFactor (derivativeOrder index) orthogonal
        (derivativeWord index) target : ℂ) •
        (((coefficientScale L sigma gamma ell grade cell
          (orthogonalDerivativeIndex index target)
          (orthogonalClosedPoint orthogonal point) : ℂ)⁻¹) •
          coefficient.1 (cell, orthogonalDerivativeIndex index target)
            (orthogonalClosedPoint orthogonal point))
  rw [coefficientScale_orthogonal]
  simp only [smul_smul]
  have nonzero :
      (coefficientScale L sigma gamma ell grade cell index point : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (coefficientScale_pos L sigma gamma ell grade cell index point).ne'
  field_simp

def coefficientReflectionOperation (L sigma gamma ell : ℝ) :
    ReflectionOperation L sigma gamma ell :=
  fun grade inputDimension outputDimension =>
    coefficientOrthogonalMap L sigma gamma ell grade inputDimension
      outputDimension planeReflectionEquiv

theorem coefficientReflection_bound
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (coefficient : Coefficient L sigma gamma ell grade
      inputDimension outputDimension) :
    ‖coefficientReflectionOperation L sigma gamma ell grade inputDimension
      outputDimension coefficient‖ ≤ reflectionBound grade * ‖coefficient‖ := by
  exact coefficientOrthogonal_bound L sigma gamma ell grade inputDimension
    outputDimension planeReflectionEquiv coefficient

theorem orthogonalClosedPoint_reflection (point : ClosedDisk) :
    orthogonalClosedPoint planeReflectionEquiv point = reflectedPoint point := by
  apply Subtype.ext
  rfl

theorem coefficientReflection_derivative
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ)
    (coefficient : Coefficient L sigma gamma ell grade
      inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative
        (coefficientReflectionOperation L sigma gamma ell grade inputDimension
          outputDimension coefficient) cell index point =
      reflectionDerivative coefficient cell index point := by
  change coefficientDerivative
      (coefficientOrthogonalMap L sigma gamma ell grade inputDimension
        outputDimension planeReflectionEquiv coefficient) cell index point = _
  rw [coefficientOrthogonal_derivative]
  unfold reflectionDerivative
  apply Finset.sum_congr rfl
  intro target _membership
  rw [orthogonalClosedPoint_reflection]

end Grad.GaugeCoefficients.Radial
