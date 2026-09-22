import DR1Jet

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue CellValues FieldL2)
open scoped BigOperators ContDiff Topology

namespace Grad.WeightedJets.Restriction

def BlockGoal : Prop :=
  ∀ (dimension order : ℕ) (smaller larger : Set Spatial)
    (inclusion : smaller ⊆ larger) (measurableLarger : MeasurableSet larger)
    (exponent : JetIndex order → ℕ),
    ‖restriction dimension order inclusion measurableLarger exponent‖ ≤ 1 ∧
    ∀ jet : WJet dimension order larger exponent,
      base dimension order smaller exponent
          (restriction dimension order inclusion measurableLarger exponent jet) =
        fieldRestriction (CellValues dimension) inclusion (base dimension order larger exponent jet) ∧
      (∀ index : JetIndex order,
        Realization.recoveredDerivative dimension order smaller exponent index
            (restriction dimension order inclusion measurableLarger exponent jet) =
          fieldRestriction (CellValues dimension) inclusion
            (Realization.recoveredDerivative dimension order larger exponent index jet)) ∧
      (∀ᵐ point ∂volume.restrict smaller, ∀ (index : JetIndex order) (cell : ℤ),
        (restriction dimension order inclusion measurableLarger exponent jet).val index point cell =
          jet.val index point cell)

theorem block_consumer : BlockGoal := fun dimension order _smaller _larger inclusion measurableLarger exponent =>
  ⟨restriction_opNorm_le dimension order inclusion measurableLarger exponent,
    fun jet => ⟨restriction_base dimension order inclusion measurableLarger exponent jet,
      fun index => restriction_recoveredDerivative dimension order inclusion measurableLarger exponent index jet,
      restriction_coordinates dimension order inclusion measurableLarger exponent jet⟩⟩

theorem fieldCellProjection_restriction (dimension : ℕ) {smaller larger : Set Spatial}
    (inclusion : smaller ⊆ larger) (cell : ℤ) (field : FieldL2 dimension larger) :
    fieldRestriction (PhysicalValue dimension) inclusion
        (Grad.GenericCarriers.fieldCellProjection dimension larger cell field) =
      Grad.GenericCarriers.fieldCellProjection dimension smaller cell
        (fieldRestriction (CellValues dimension) inclusion field) :=
  fieldRestriction_naturality (CellValues dimension) (PhysicalValue dimension)
    (Grad.GenericCarriers.cellProjection (PhysicalValue dimension) cell) inclusion field

theorem restriction_norm_sq (dimension order : ℕ) {smaller larger : Set Spatial}
    (inclusion : smaller ⊆ larger) (measurableLarger : MeasurableSet larger)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order larger exponent) :
    ‖restriction dimension order inclusion measurableLarger exponent jet‖ ^ 2 =
      ∑ index : JetIndex order, ∫ point in smaller, ‖jet.val index point‖ ^ 2 := by
  rw [jet_norm_sq]
  apply Finset.sum_congr rfl
  intro index _membership
  rw [Grad.GenericCarriers.domainL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [fieldRestriction_ae (CellValues dimension) inclusion (jet.val index)]
    with point represented
  change ‖fieldRestriction (CellValues dimension) inclusion (jet.val index) point‖ ^ 2 = _
  rw [represented]

theorem restriction_tendsto (dimension order : ℕ) {smaller larger : Set Spatial}
    (inclusion : smaller ⊆ larger) (measurableLarger : MeasurableSet larger)
    (exponent : JetIndex order → ℕ) {Index : Type*} {filter : Filter Index}
    {approximants : Index → WJet dimension order larger exponent}
    {jet : WJet dimension order larger exponent}
    (convergence : Filter.Tendsto approximants filter (𝓝 jet)) :
    Filter.Tendsto
      (fun index => restriction dimension order inclusion measurableLarger exponent (approximants index))
      filter (𝓝 (restriction dimension order inclusion measurableLarger exponent jet)) :=
  ((restriction dimension order inclusion measurableLarger exponent).continuous.tendsto jet).comp convergence

theorem zeroDimension (order : ℕ) {smaller larger : Set Spatial}
    (inclusion : smaller ⊆ larger) (measurableLarger : MeasurableSet larger)
    (exponent : JetIndex order → ℕ) :
    ‖restriction 0 order inclusion measurableLarger exponent‖ ≤ 1 :=
  restriction_opNorm_le 0 order inclusion measurableLarger exponent

theorem zeroOrder (dimension : ℕ) {smaller larger : Set Spatial}
    (inclusion : smaller ⊆ larger) (measurableLarger : MeasurableSet larger)
    (exponent : JetIndex 0 → ℕ) (jet : WJet dimension 0 larger exponent) :
    base dimension 0 smaller exponent (restriction dimension 0 inclusion measurableLarger exponent jet) =
      fieldRestriction (CellValues dimension) inclusion (base dimension 0 larger exponent jet) :=
  restriction_base dimension 0 inclusion measurableLarger exponent jet

end Grad.WeightedJets.Restriction
