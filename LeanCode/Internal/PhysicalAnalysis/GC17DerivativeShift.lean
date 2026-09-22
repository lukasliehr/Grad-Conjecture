import GC17FixedFamily

noncomputable section

set_option maxHeartbeats 1400000

open Set
open scoped BigOperators ENNReal Topology

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

def raisedDerivativeIndex {grade : ℕ} (fixed : CartesianMultiIndex) (index : DerivativeIndex grade) :
    DerivativeIndex (grade + cartesianOrder fixed) :=
  ⟨(⟨index.val.1.val + fixed.1, by have := index.property; unfold cartesianOrder; omega⟩,
    ⟨index.val.2.val + fixed.2, by have := index.property; unfold cartesianOrder; omega⟩), by
      have := index.property
      change index.val.1.val + fixed.1 + (index.val.2.val + fixed.2) ≤ grade + (fixed.1 + fixed.2)
      omega⟩

theorem raisedDerivativeIndex_order {grade : ℕ} (fixed : CartesianMultiIndex) (index : DerivativeIndex grade) :
    derivativeOrder (raisedDerivativeIndex fixed index) = derivativeOrder index + cartesianOrder fixed := by
  simp only [derivativeOrder, raisedDerivativeIndex, cartesianOrder]
  omega

theorem coefficientScale_raisedDerivative (L sigma gamma ell : ℝ) {grade : ℕ}
    (fixed : CartesianMultiIndex) (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientScale L sigma gamma ell (grade + cartesianOrder fixed) cell
      (raisedDerivativeIndex fixed index) point = coefficientScale L sigma gamma ell grade cell index point := by
  unfold coefficientScale
  rw [raisedDerivativeIndex_order]
  have exponent : grade + cartesianOrder fixed - (derivativeOrder index + cartesianOrder fixed) =
      grade - derivativeOrder index := by omega
  rw [exponent]

def rawDerivativeShift {grade input output : ℕ} (fixed : CartesianMultiIndex)
    (coefficient : WeightedAmbient (grade + cartesianOrder fixed) input output) : WeightedAmbient grade input output := by
  refine ⟨fun pair => coefficient (pair.1, raisedDerivativeIndex fixed pair.2), ?_⟩
  apply memℓp_gen
  have swapped : Summable (fun pair : DerivativeIndex grade × ℤ =>
      ‖coefficient (pair.2, raisedDerivativeIndex fixed pair.1)‖) := by
    apply (summable_prod_of_nonneg (fun pair => norm_nonneg
      (coefficient (pair.2, raisedDerivativeIndex fixed pair.1)))).2
    exact ⟨fun index => coordinate_norm_summable coefficient (raisedDerivativeIndex fixed index),
      (hasSum_fintype _).summable⟩
  have all : Summable (fun pair : ℤ × DerivativeIndex grade =>
      ‖coefficient (pair.1, raisedDerivativeIndex fixed pair.2)‖) :=
    (Equiv.prodComm (DerivativeIndex grade) ℤ).summable_iff.mp swapped
  have oneToReal : (1 : ℝ≥0∞).toReal = 1 := by norm_num
  simpa only [oneToReal, Real.rpow_one] using all

theorem rawDerivativeShift_norm_le {grade input output : ℕ} (fixed : CartesianMultiIndex)
    (coefficient : WeightedAmbient (grade + cartesianOrder fixed) input output) :
    ‖rawDerivativeShift fixed coefficient‖ ≤ (Fintype.card (DerivativeIndex grade) : ℝ) * ‖coefficient‖ := by
  rw [ambient_norm_formula]
  calc
    _ ≤ ∑ _ : DerivativeIndex grade, ‖coefficient‖ := by
      apply Finset.sum_le_sum
      intro index _
      exact coordinate_norm_sum_le coefficient (raisedDerivativeIndex fixed index)
    _ = _ := by simp

def rawDerivativeShiftLinear (grade input output : ℕ) (fixed : CartesianMultiIndex) :
    WeightedAmbient (grade + cartesianOrder fixed) input output →ₗ[ℂ] WeightedAmbient grade input output where
  toFun := rawDerivativeShift fixed
  map_add' first second := by apply lp.ext; rfl
  map_smul' scalar coefficient := by apply lp.ext; rfl

def rawDerivativeShiftMap (grade input output : ℕ) (fixed : CartesianMultiIndex) :
    WeightedAmbient (grade + cartesianOrder fixed) input output →L[ℂ] WeightedAmbient grade input output :=
  (rawDerivativeShiftLinear grade input output fixed).mkContinuous
    (Fintype.card (DerivativeIndex grade) : ℝ) (rawDerivativeShift_norm_le fixed)

theorem rawDerivativeShift_weightedSingle (L sigma gamma ell : ℝ) (grade : ℕ)
    {input output : ℕ} (fixed : CartesianMultiIndex) (cell : ℤ) (field : SmoothOperatorJet input output) :
    rawDerivativeShift fixed (weightedSingle L sigma gamma ell (grade + cartesianOrder fixed) cell field) =
      weightedSingle L sigma gamma ell grade cell (shiftedOperatorJet field fixed) := by
  apply lp.ext
  funext pair
  rcases pair with ⟨other, index⟩
  change weightedSingle L sigma gamma ell (grade + cartesianOrder fixed) cell field
    (other, raisedDerivativeIndex fixed index) = _
  by_cases same : other = cell
  · subst other
    rw [weightedSingle_apply_same, weightedSingle_apply_same]
    apply ContinuousMap.ext
    intro point
    change (coefficientScale L sigma gamma ell (grade + cartesianOrder fixed) cell
        (raisedDerivativeIndex fixed index) point : ℂ) •
        smoothOperatorDerivative field (derivativeMultiIndex (raisedDerivativeIndex fixed index)) point =
      (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
        smoothOperatorDerivative (shiftedOperatorJet field fixed) (derivativeMultiIndex index) point
    rw [coefficientScale_raisedDerivative, shiftedOperatorJet_derivative]
    rfl
  · rw [weightedSingle_apply, weightedSingle_apply]
    simp only [same, ite_false]

theorem rawDerivativeShift_mem_smoothCore (L sigma gamma ell : ℝ) (grade input output : ℕ)
    (fixed : CartesianMultiIndex)
    (coefficient : smoothCore L sigma gamma ell (grade + cartesianOrder fixed) input output) :
    rawDerivativeShift fixed coefficient.val ∈ smoothCore L sigma gamma ell grade input output := by
  let target := smoothCore L sigma gamma ell grade input output
  refine Submodule.span_induction
    (p := fun value _ => rawDerivativeShift fixed value ∈ target) ?_ ?_ ?_ ?_ coefficient.property
  · intro generator membership
    rcases membership with ⟨pair, rfl⟩
    rw [rawDerivativeShift_weightedSingle]
    exact Submodule.subset_span (Set.mem_range.mpr ⟨(pair.1, shiftedOperatorJet pair.2 fixed), rfl⟩)
  · change rawDerivativeShiftLinear grade input output fixed 0 ∈ target
    rw [map_zero]
    exact target.zero_mem
  · intro first second _ _ firstIn secondIn
    change rawDerivativeShiftLinear grade input output fixed (first + second) ∈ target
    rw [map_add]
    exact target.add_mem firstIn secondIn
  · intro scalar value _ valueIn
    change rawDerivativeShiftLinear grade input output fixed (scalar • value) ∈ target
    rw [map_smul]
    exact target.smul_mem scalar valueIn

theorem rawDerivativeShift_closure (L sigma gamma ell : ℝ) (grade input output : ℕ)
    (fixed : CartesianMultiIndex)
    (coefficient : Coefficient L sigma gamma ell (grade + cartesianOrder fixed) input output) :
    rawDerivativeShift fixed coefficient.val ∈
      (smoothCore L sigma gamma ell grade input output).topologicalClosure := by
  let source := smoothCore L sigma gamma ell (grade + cartesianOrder fixed) input output
  let target := smoothCore L sigma gamma ell grade input output
  let operation := rawDerivativeShiftMap grade input output fixed
  have sourceMap : source.map (operation : _ →ₗ[ℂ] _) ≤ target := by
    intro value membership
    rcases membership with ⟨argument, inside, rfl⟩
    exact rawDerivativeShift_mem_smoothCore L sigma gamma ell grade input output fixed ⟨argument, inside⟩
  have mapped : operation coefficient.val ∈ source.topologicalClosure.map (operation : _ →ₗ[ℂ] _) :=
    ⟨coefficient.val, coefficient.property, rfl⟩
  exact (Submodule.topologicalClosure_mono sourceMap) ((source.topologicalClosure_map operation) mapped)

def coefficientDerivativeShift (L sigma gamma ell : ℝ) (grade input output : ℕ)
    (fixed : CartesianMultiIndex)
    (coefficient : Coefficient L sigma gamma ell (grade + cartesianOrder fixed) input output) :
    Coefficient L sigma gamma ell grade input output :=
  ⟨rawDerivativeShift fixed coefficient.val,
    rawDerivativeShift_closure L sigma gamma ell grade input output fixed coefficient⟩

theorem coefficientDerivativeShift_norm_le (L sigma gamma ell : ℝ) (grade input output : ℕ)
    (fixed : CartesianMultiIndex)
    (coefficient : Coefficient L sigma gamma ell (grade + cartesianOrder fixed) input output) :
    ‖coefficientDerivativeShift L sigma gamma ell grade input output fixed coefficient‖ ≤
      (Fintype.card (DerivativeIndex grade) : ℝ) * ‖coefficient‖ :=
  rawDerivativeShift_norm_le fixed coefficient.val

theorem coefficientDerivativeShift_derivative (L sigma gamma ell : ℝ) (grade input output : ℕ)
    (fixed : CartesianMultiIndex)
    (coefficient : Coefficient L sigma gamma ell (grade + cartesianOrder fixed) input output)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (coefficientDerivativeShift L sigma gamma ell grade input output fixed coefficient)
      cell index point = coefficientDerivative coefficient cell (raisedDerivativeIndex fixed index) point := by
  change ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
      coefficient.val (cell, raisedDerivativeIndex fixed index) point =
    ((coefficientScale L sigma gamma ell (grade + cartesianOrder fixed) cell
      (raisedDerivativeIndex fixed index) point : ℂ)⁻¹) •
        coefficient.val (cell, raisedDerivativeIndex fixed index) point
  rw [coefficientScale_raisedDerivative]

def derivativeFamily {L sigma gamma ell : ℝ} {input output : ℕ}
    (fixed : CartesianMultiIndex) (family : CoefficientFamily L sigma gamma ell input output) :
    CoefficientFamily L sigma gamma ell input output :=
  fun grade => coefficientDerivativeShift L sigma gamma ell grade input output fixed
    (family (grade + cartesianOrder fixed))

theorem derivativeFamily_coherent {L sigma gamma ell : ℝ} {input output : ℕ}
    (fixed : CartesianMultiIndex) (family : CoefficientFamily L sigma gamma ell input output)
    (coherent : FamilyCoherent family) : FamilyCoherent (derivativeFamily fixed family) := by
  intro grade other index otherIndex same cell point
  change coefficientDerivative (coefficientDerivativeShift _ _ _ _ _ _ _ _ _) _ _ _ =
    coefficientDerivative (coefficientDerivativeShift _ _ _ _ _ _ _ _ _) _ _ _
  rw [coefficientDerivativeShift_derivative, coefficientDerivativeShift_derivative]
  apply coherent _ _ _ _ _ cell point
  exact congrArg (fun multi => shiftedOperatorIndex multi fixed) same

end Grad.GaugeCoefficients.Physical.Ledger
