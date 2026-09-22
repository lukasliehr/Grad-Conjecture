import DR1Field

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue CellValues FieldL2)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.Restriction

variable {smaller larger : Set Spatial}

def restrictTuple (dimension order : ℕ) (inclusion : smaller ⊆ larger)
    (tuple : JetTuple dimension order larger) : JetTuple dimension order smaller :=
  WithLp.toLp 2 (fun index => fieldRestriction (CellValues dimension) inclusion (tuple index))

theorem restrictTuple_base (dimension order : ℕ) (inclusion : smaller ⊆ larger)
    (exponent : JetIndex order → ℕ) (tuple : JetTuple dimension order larger) :
    ambientBase dimension order smaller exponent (restrictTuple dimension order inclusion tuple) =
      fieldRestriction (CellValues dimension) inclusion (ambientBase dimension order larger exponent tuple) :=
  (fieldRestriction_inverse dimension inclusion (exponent (zeroIndex order)) (tuple (zeroIndex order))).symm

theorem restrictTuple_mem (dimension order : ℕ) (inclusion : smaller ⊆ larger)
    (measurableLarger : MeasurableSet larger) (exponent : JetIndex order → ℕ)
    (tuple : JetTuple dimension order larger)
    (membership : tuple ∈ jetGraph dimension order larger exponent) :
    restrictTuple dimension order inclusion tuple ∈ jetGraph dimension order smaller exponent := by
  apply (jetGraph_mem dimension order smaller exponent _).mpr
  intro index cell vector test
  change testPairing dimension smaller cell vector test
    (fieldRestriction (CellValues dimension) inclusion (tuple index)) = _
  rw [testPairing_restriction dimension inclusion measurableLarger, restrictTuple_base,
    derivativeTestPairing_restriction dimension order inclusion measurableLarger]
  exact (jetGraph_mem dimension order larger exponent tuple).mp membership
    index cell vector (widenTest inclusion test)

theorem restrictTuple_norm_le (dimension order : ℕ) (inclusion : smaller ⊆ larger)
    (tuple : JetTuple dimension order larger) :
    ‖restrictTuple dimension order inclusion tuple‖ ≤ ‖tuple‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [tuple_norm_sq, tuple_norm_sq]
  apply Finset.sum_le_sum
  intro index _membership
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (fieldRestriction_norm_le (CellValues dimension) inclusion (tuple index))

def restrictionLinear (dimension order : ℕ) (inclusion : smaller ⊆ larger)
    (measurableLarger : MeasurableSet larger) (exponent : JetIndex order → ℕ) :
    WJet dimension order larger exponent →ₗ[ℂ] WJet dimension order smaller exponent where
  toFun jet := ⟨restrictTuple dimension order inclusion jet.val,
    restrictTuple_mem dimension order inclusion measurableLarger exponent jet.val jet.property⟩
  map_add' first second := by
    apply jet_eq
    intro index
    exact map_add (fieldRestriction (CellValues dimension) inclusion) (first.val index) (second.val index)
  map_smul' scalar jet := by
    apply jet_eq
    intro index
    exact map_smul (fieldRestriction (CellValues dimension) inclusion) scalar (jet.val index)

def restriction (dimension order : ℕ) (inclusion : smaller ⊆ larger)
    (measurableLarger : MeasurableSet larger) (exponent : JetIndex order → ℕ) :
    WJet dimension order larger exponent →L[ℂ] WJet dimension order smaller exponent :=
  (restrictionLinear dimension order inclusion measurableLarger exponent).mkContinuous 1 (fun jet => by
    change ‖restrictTuple dimension order inclusion jet.val‖ ≤ 1 * ‖jet.val‖
    simpa only [one_mul] using restrictTuple_norm_le dimension order inclusion jet.val)

theorem restriction_apply (dimension order : ℕ) (inclusion : smaller ⊆ larger)
    (measurableLarger : MeasurableSet larger) (exponent : JetIndex order → ℕ)
    (jet : WJet dimension order larger exponent) :
    (restriction dimension order inclusion measurableLarger exponent jet).val =
      restrictTuple dimension order inclusion jet.val := rfl

theorem restriction_norm_le (dimension order : ℕ) (inclusion : smaller ⊆ larger)
    (measurableLarger : MeasurableSet larger) (exponent : JetIndex order → ℕ)
    (jet : WJet dimension order larger exponent) :
    ‖restriction dimension order inclusion measurableLarger exponent jet‖ ≤ ‖jet‖ :=
  restrictTuple_norm_le dimension order inclusion jet.val

theorem restriction_opNorm_le (dimension order : ℕ) (inclusion : smaller ⊆ larger)
    (measurableLarger : MeasurableSet larger) (exponent : JetIndex order → ℕ) :
    ‖restriction dimension order inclusion measurableLarger exponent‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro jet
  simpa only [one_mul] using restriction_norm_le dimension order inclusion measurableLarger exponent jet

theorem restriction_base (dimension order : ℕ) (inclusion : smaller ⊆ larger)
    (measurableLarger : MeasurableSet larger) (exponent : JetIndex order → ℕ)
    (jet : WJet dimension order larger exponent) :
    base dimension order smaller exponent (restriction dimension order inclusion measurableLarger exponent jet) =
      fieldRestriction (CellValues dimension) inclusion (base dimension order larger exponent jet) :=
  restrictTuple_base dimension order inclusion exponent jet.val

theorem restriction_recoveredDerivative (dimension order : ℕ) (inclusion : smaller ⊆ larger)
    (measurableLarger : MeasurableSet larger) (exponent : JetIndex order → ℕ)
    (index : JetIndex order) (jet : WJet dimension order larger exponent) :
    Realization.recoveredDerivative dimension order smaller exponent index
        (restriction dimension order inclusion measurableLarger exponent jet) =
      fieldRestriction (CellValues dimension) inclusion
        (Realization.recoveredDerivative dimension order larger exponent index jet) :=
  (fieldRestriction_inverse dimension inclusion (exponent index) (jet.val index)).symm

theorem restriction_coordinates (dimension order : ℕ) (inclusion : smaller ⊆ larger)
    (measurableLarger : MeasurableSet larger) (exponent : JetIndex order → ℕ)
    (jet : WJet dimension order larger exponent) :
    ∀ᵐ point ∂volume.restrict smaller, ∀ (index : JetIndex order) (cell : ℤ),
      (restriction dimension order inclusion measurableLarger exponent jet).val index point cell =
        jet.val index point cell := by
  have represented : ∀ᵐ point ∂volume.restrict smaller, ∀ index : JetIndex order,
      fieldRestriction (CellValues dimension) inclusion (jet.val index) point = jet.val index point :=
    ae_all_iff.mpr (fun index => fieldRestriction_ae (CellValues dimension) inclusion (jet.val index))
  filter_upwards [represented] with point representedAt
  intro index cell
  exact congrArg (fun values : CellValues dimension => values cell) (representedAt index)

theorem restriction_self (dimension order : ℕ) (domain : Set Spatial)
    (measurableDomain : MeasurableSet domain) (exponent : JetIndex order → ℕ) :
    restriction dimension order (Set.Subset.rfl : domain ⊆ domain) measurableDomain exponent =
      ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro jet
  apply jet_eq
  intro index
  change fieldRestriction (CellValues dimension) (Set.Subset.rfl : domain ⊆ domain) (jet.val index) = _
  rw [fieldRestriction_self]
  rfl

theorem restriction_comp (dimension order : ℕ) {small middle large : Set Spatial}
    (first : small ⊆ middle) (second : middle ⊆ large)
    (measurableMiddle : MeasurableSet middle) (measurableLarge : MeasurableSet large)
    (exponent : JetIndex order → ℕ) :
    (restriction dimension order first measurableMiddle exponent).comp
        (restriction dimension order second measurableLarge exponent) =
      restriction dimension order (first.trans second) measurableLarge exponent := by
  apply ContinuousLinearMap.ext
  intro jet
  apply jet_eq
  intro index
  exact congrArg (fun mapping : FieldL2 dimension large →L[ℂ] FieldL2 dimension small =>
    mapping (jet.val index)) (fieldRestriction_comp (CellValues dimension) first second)

theorem restriction_inclusion (dimension lower higher : ℕ) (inclusion : smaller ⊆ larger)
    (measurableLarger : MeasurableSet larger) (gap : ℕ) (bound : lower ≤ higher)
    (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ)
    (compatible : Inclusions.Compatible bound gap source target)
    (jet : WJet dimension higher larger source) :
    restriction dimension lower inclusion measurableLarger target
        (Inclusions.inclusion dimension lower higher larger gap bound source target compatible jet) =
      Inclusions.inclusion dimension lower higher smaller gap bound source target compatible
        (restriction dimension higher inclusion measurableLarger source jet) := by
  apply jet_eq
  intro index
  exact fieldRestriction_inverse dimension inclusion gap (jet.val (Inclusions.indexInclusion bound index))

theorem restriction_weak_integral (dimension order : ℕ) (inclusion : smaller ⊆ larger)
    (measurableLarger : MeasurableSet larger) (exponent : JetIndex order → ℕ)
    (index : JetIndex order) (jet : WJet dimension order larger exponent)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction smaller) :
    (∫ point in smaller, test.toFun point • inner ℂ vector
      (Realization.recoveredDerivative dimension order smaller exponent index
        (restriction dimension order inclusion measurableLarger exponent jet) point cell)) =
      (-1 : ℂ) ^ degree index * ∫ point in smaller,
        Grad.WeakTesting.orderedTestDerivative (degree index) (derivativeWord index) test.toFun point •
          inner ℂ vector (fieldRestriction (CellValues dimension) inclusion
            (base dimension order larger exponent jet) point cell) := by
  rw [← restriction_base dimension order inclusion measurableLarger exponent]
  exact Realization.recoveredDerivative_integral dimension order smaller exponent index
    (restriction dimension order inclusion measurableLarger exponent jet) cell vector test

theorem graphGrade_consumer (dimension order weight : ℕ) (inclusion : smaller ⊆ larger)
    (measurableLarger : MeasurableSet larger) (jet : GraphGrade dimension order weight larger) :
    ‖restriction dimension order inclusion measurableLarger (fun _ => weight) jet‖ ≤ ‖jet‖ :=
  restriction_norm_le dimension order inclusion measurableLarger _ jet

theorem mixed_consumer (dimension grade : ℕ) (inclusion : smaller ⊆ larger)
    (measurableLarger : MeasurableSet larger) (jet : Mixed dimension grade larger) :
    ‖restriction dimension grade inclusion measurableLarger (fun index => grade - degree index) jet‖ ≤ ‖jet‖ :=
  restriction_norm_le dimension grade inclusion measurableLarger _ jet

end Grad.WeightedJets.Restriction
