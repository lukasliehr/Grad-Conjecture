import ZE1Support
import ZE1Coherence

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues FieldL2)
open scoped BigOperators

namespace Grad.WeightedJets.ZeroExtension

set_option maxHeartbeats 1200000

open Classical in
def BlockGoal : Prop :=
  ∀ (dimension order : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (exponent : JetIndex order → ℕ),
    Function.Injective (jetExtension dimension order domain support measurable localizer exponent) ∧
    ‖(jetExtension dimension order domain support measurable localizer exponent).toContinuousLinearMap‖ ≤ 1 ∧
    ∀ jet : supportedJetSubmodule dimension order domain support exponent,
      ‖jetExtension dimension order domain support measurable localizer exponent jet‖ = ‖jet‖ ∧
      Restriction.restriction dimension order (Set.subset_univ domain) MeasurableSet.univ exponent
          (jetExtension dimension order domain support measurable localizer exponent jet) = jet.val ∧
      base dimension order Set.univ exponent
          (jetExtension dimension order domain support measurable localizer exponent jet) =
        fieldExtension (CellValues dimension) domain measurable (base dimension order domain exponent jet.val) ∧
      (∀ index : JetIndex order,
        Realization.recoveredDerivative dimension order Set.univ exponent index
            (jetExtension dimension order domain support measurable localizer exponent jet) =
          fieldExtension (CellValues dimension) domain measurable
            (Realization.recoveredDerivative dimension order domain exponent index jet.val)) ∧
      (∀ᵐ point ∂volume, ∀ (index : JetIndex order) (cell : ℤ),
        (jetExtension dimension order domain support measurable localizer exponent jet).val index point cell =
          if point ∈ domain then jet.val.val index point cell else 0)

theorem block_consumer : BlockGoal := by
  intro dimension order domain support measurable localizer exponent
  refine ⟨jetExtension_injective dimension order domain support measurable localizer exponent,
    jetExtension_opNorm_le dimension order domain support measurable localizer exponent, ?_⟩
  intro jet
  exact ⟨extendJet_norm dimension order domain support measurable localizer exponent jet.val jet.property,
    restriction_extendJet dimension order domain support measurable localizer exponent jet.val jet.property,
    extendJet_base dimension order domain support measurable localizer exponent jet.val jet.property,
    fun index => extendJet_recoveredDerivative dimension order domain support measurable localizer exponent
      jet.val jet.property index,
    extendJet_coordinates dimension order domain support measurable localizer exponent jet.val jet.property⟩

theorem fieldCellProjection_extension (dimension : ℕ) (domain : Set Spatial)
    (measurable : MeasurableSet domain) (cell : ℤ) (field : FieldL2 dimension domain) :
    fieldExtension (Grad.GenericCarriers.PhysicalValue dimension) domain measurable
        (Grad.GenericCarriers.fieldCellProjection dimension domain cell field) =
      Grad.GenericCarriers.fieldCellProjection dimension Set.univ cell
        (fieldExtension (CellValues dimension) domain measurable field) :=
  fieldExtension_naturality (CellValues dimension) domain measurable
    (Grad.GenericCarriers.cellProjection (Grad.GenericCarriers.PhysicalValue dimension) cell) field

theorem cutoff_stored_support (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : SpatialMultiplier.Symbol order domain)
    (exponent : JetIndex order → ℕ) (compatible : SpatialMultiplier.ExponentAntitone exponent)
    (jet : WJet dimension order domain exponent) :
    ∀ index : JetIndex order, ∀ᵐ point ∂volume.restrict domain,
      point ∉ tsupport symbol.toFun →
        (SpatialMultiplier.jetMultiplier dimension order domain openDomain symbol exponent compatible jet).val
          index point = 0 :=
  jetMultiplier_supported dimension order domain openDomain symbol exponent compatible jet

end Grad.WeightedJets.ZeroExtension

