import ZE1Jet

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues FieldL2)

namespace Grad.WeightedJets.ZeroExtension

set_option maxHeartbeats 1200000

theorem tupleSupported_zero (dimension order : ℕ) (domain support : Set Spatial) :
    TupleSupported dimension order domain support 0 := by
  intro index
  filter_upwards [Lp.coeFn_zero (CellValues dimension) 2 (volume.restrict domain)] with point zeroAt
  intro _outside
  exact zeroAt

theorem tupleSupported_add (dimension order : ℕ) (domain support : Set Spatial)
    (first second : JetTuple dimension order domain)
    (firstSupported : TupleSupported dimension order domain support first)
    (secondSupported : TupleSupported dimension order domain support second) :
    TupleSupported dimension order domain support (first + second) := by
  intro index
  filter_upwards [firstSupported index, secondSupported index,
    Lp.coeFn_add (first index) (second index)] with point firstAt secondAt summedAt
  intro outside
  change (first index + second index) point = 0
  rw [summedAt, Pi.add_apply, firstAt outside, secondAt outside, add_zero]

theorem tupleSupported_smul (dimension order : ℕ) (domain support : Set Spatial)
    (scalar : ℂ) (tuple : JetTuple dimension order domain)
    (supported : TupleSupported dimension order domain support tuple) :
    TupleSupported dimension order domain support (scalar • tuple) := by
  intro index
  filter_upwards [supported index, Lp.coeFn_smul scalar (tuple index)]
    with point zeroAt scaledAt
  intro outside
  change (scalar • tuple index) point = 0
  rw [scaledAt, Pi.smul_apply, zeroAt outside, smul_zero]

abbrev supportedJetSubmodule (dimension order : ℕ) (domain support : Set Spatial)
    (exponent : JetIndex order → ℕ) : Submodule ℂ (WJet dimension order domain exponent) where
  carrier := {jet | TupleSupported dimension order domain support jet.val}
  zero_mem' := tupleSupported_zero dimension order domain support
  add_mem' := fun {first second} firstSupported secondSupported =>
    tupleSupported_add dimension order domain support first.val second.val firstSupported secondSupported
  smul_mem' := fun scalar jet supported =>
    tupleSupported_smul dimension order domain support scalar jet.val supported

instance supportedJetNormedSpace (dimension order : ℕ) (domain support : Set Spatial)
    (exponent : JetIndex order → ℕ) :
    NormedSpace ℂ (supportedJetSubmodule dimension order domain support exponent) where
  norm_smul_le scalar jet := norm_smul_le scalar jet.val

def jetExtension (dimension order : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (exponent : JetIndex order → ℕ) :
    supportedJetSubmodule dimension order domain support exponent →ₗᵢ[ℂ]
      WJet dimension order Set.univ exponent where
  toFun jet := extendJet dimension order domain support measurable localizer exponent jet.val jet.property
  map_add' first second := by
    apply jet_eq
    intro index
    exact map_add (fieldExtension (CellValues dimension) domain measurable)
      (first.val.val index) (second.val.val index)
  map_smul' scalar jet := by
    apply jet_eq
    intro index
    exact map_smul (fieldExtension (CellValues dimension) domain measurable) scalar (jet.val.val index)
  norm_map' jet := extendJet_norm dimension order domain support measurable localizer exponent jet.val jet.property

theorem jetExtension_restriction (dimension order : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (exponent : JetIndex order → ℕ) :
    (Restriction.restriction dimension order (Set.subset_univ domain) MeasurableSet.univ exponent).comp
        (jetExtension dimension order domain support measurable localizer exponent).toContinuousLinearMap =
      (supportedJetSubmodule dimension order domain support exponent).subtypeL := by
  apply ContinuousLinearMap.ext
  intro jet
  exact restriction_extendJet dimension order domain support measurable localizer exponent jet.val jet.property

theorem jetExtension_opNorm_le (dimension order : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (exponent : JetIndex order → ℕ) :
    ‖(jetExtension dimension order domain support measurable localizer exponent).toContinuousLinearMap‖ ≤ 1 := by
  let : NormedSpace ℂ (supportedJetSubmodule dimension order domain support exponent) :=
    supportedJetNormedSpace dimension order domain support exponent
  exact LinearIsometry.norm_toContinuousLinearMap_le
    (jetExtension dimension order domain support measurable localizer exponent)

theorem jetExtension_injective (dimension order : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (exponent : JetIndex order → ℕ) :
    Function.Injective (jetExtension dimension order domain support measurable localizer exponent) :=
  (jetExtension dimension order domain support measurable localizer exponent).injective

theorem jetExtension_weak (dimension order : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (exponent : JetIndex order → ℕ)
    (jet : supportedJetSubmodule dimension order domain support exponent) (index : JetIndex order)
    (cell : ℤ) (vector : Grad.GenericCarriers.PhysicalValue dimension) (test : TestFunction Set.univ) :
    testPairing dimension Set.univ cell vector test
      (fieldExtension (CellValues dimension) domain measurable
        (Realization.recoveredDerivative dimension order domain exponent index jet.val)) =
      (-1 : ℂ) ^ degree index * derivativeTestPairing dimension order Set.univ index cell vector test
        (fieldExtension (CellValues dimension) domain measurable (base dimension order domain exponent jet.val)) := by
  rw [← extendJet_base dimension order domain support measurable localizer exponent jet.val jet.property,
    ← extendJet_recoveredDerivative dimension order domain support measurable localizer exponent
      jet.val jet.property index]
  exact Realization.recoveredDerivative_weak dimension order Set.univ exponent index
    (extendJet dimension order domain support measurable localizer exponent jet.val jet.property)
    cell vector test

end Grad.WeightedJets.ZeroExtension
