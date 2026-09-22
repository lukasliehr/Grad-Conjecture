import ZE1Localization
import DR1Jet

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues FieldL2)
open scoped BigOperators

namespace Grad.WeightedJets.ZeroExtension

def TupleSupported (dimension order : ℕ) (domain support : Set Spatial)
    (tuple : JetTuple dimension order domain) : Prop :=
  ∀ index : JetIndex order, SupportedField (CellValues dimension) domain support (tuple index)

def extendTuple (dimension order : ℕ) (domain : Set Spatial) (measurable : MeasurableSet domain)
    (tuple : JetTuple dimension order domain) : JetTuple dimension order Set.univ :=
  WithLp.toLp 2 (fun index => fieldExtension (CellValues dimension) domain measurable (tuple index))

theorem ambientBase_supported (dimension order : ℕ) (domain support : Set Spatial)
    (exponent : JetIndex order → ℕ) (tuple : JetTuple dimension order domain)
    (supported : TupleSupported dimension order domain support tuple) :
    SupportedField (CellValues dimension) domain support
      (ambientBase dimension order domain exponent tuple) := by
  filter_upwards [supported (zeroIndex order),
    Grad.CellWeights.inverseFieldCLM_ae dimension domain (exponent (zeroIndex order))
      (tuple (zeroIndex order))] with point zeroAt represented
  intro outside
  change Grad.CellWeights.inverseFieldCLM dimension domain (exponent (zeroIndex order))
    (tuple (zeroIndex order)) point = 0
  rw [represented, zeroAt outside, map_zero]

theorem extendTuple_base (dimension order : ℕ) (domain : Set Spatial)
    (measurable : MeasurableSet domain) (exponent : JetIndex order → ℕ)
    (tuple : JetTuple dimension order domain) :
    ambientBase dimension order Set.univ exponent (extendTuple dimension order domain measurable tuple) =
      fieldExtension (CellValues dimension) domain measurable
        (ambientBase dimension order domain exponent tuple) :=
  (fieldExtension_inverse dimension domain measurable (exponent (zeroIndex order))
    (tuple (zeroIndex order))).symm

theorem extendTuple_norm (dimension order : ℕ) (domain : Set Spatial)
    (measurable : MeasurableSet domain) (tuple : JetTuple dimension order domain) :
    ‖extendTuple dimension order domain measurable tuple‖ = ‖tuple‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [tuple_norm_sq, tuple_norm_sq]
  apply Finset.sum_congr rfl
  intro index _membership
  exact congrArg (fun norm : ℝ => norm ^ 2)
    (fieldExtension_norm (CellValues dimension) domain measurable (tuple index))

theorem extendTuple_mem (dimension order : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order domain exponent)
    (supported : TupleSupported dimension order domain support jet.val) :
    extendTuple dimension order domain measurable jet.val ∈ jetGraph dimension order Set.univ exponent := by
  apply (jetGraph_mem dimension order Set.univ exponent _).mpr
  intro index cell vector test
  change testPairing dimension Set.univ cell vector test
    (fieldExtension (CellValues dimension) domain measurable (jet.val index)) = _
  rw [testPairing_extension dimension measurable localizer (jet.val index) (supported index),
    extendTuple_base,
    derivativeTestPairing_extension dimension order measurable localizer
      (ambientBase dimension order domain exponent jet.val)
      (ambientBase_supported dimension order domain support exponent jet.val supported)]
  exact (jetGraph_mem dimension order domain exponent jet.val).mp jet.property
    index cell vector (localizeTest localizer test)

def extendJet (dimension order : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order domain exponent)
    (supported : TupleSupported dimension order domain support jet.val) :
    WJet dimension order Set.univ exponent :=
  ⟨extendTuple dimension order domain measurable jet.val,
    extendTuple_mem dimension order domain support measurable localizer exponent jet supported⟩

theorem extendJet_norm (dimension order : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order domain exponent)
    (supported : TupleSupported dimension order domain support jet.val) :
    ‖extendJet dimension order domain support measurable localizer exponent jet supported‖ = ‖jet‖ :=
  extendTuple_norm dimension order domain measurable jet.val

theorem extendJet_base (dimension order : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order domain exponent)
    (supported : TupleSupported dimension order domain support jet.val) :
    base dimension order Set.univ exponent
        (extendJet dimension order domain support measurable localizer exponent jet supported) =
      fieldExtension (CellValues dimension) domain measurable (base dimension order domain exponent jet) :=
  extendTuple_base dimension order domain measurable exponent jet.val

theorem extendJet_recoveredDerivative (dimension order : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order domain exponent)
    (supported : TupleSupported dimension order domain support jet.val) (index : JetIndex order) :
    Realization.recoveredDerivative dimension order Set.univ exponent index
        (extendJet dimension order domain support measurable localizer exponent jet supported) =
      fieldExtension (CellValues dimension) domain measurable
        (Realization.recoveredDerivative dimension order domain exponent index jet) :=
  (fieldExtension_inverse dimension domain measurable (exponent index) (jet.val index)).symm

open Classical in
theorem extendJet_coordinates (dimension order : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order domain exponent)
    (supported : TupleSupported dimension order domain support jet.val) :
    ∀ᵐ point ∂volume, ∀ (index : JetIndex order) (cell : ℤ),
      (extendJet dimension order domain support measurable localizer exponent jet supported).val index point cell =
        if point ∈ domain then jet.val index point cell else 0 := by
  classical
  have represented := ae_all_iff.mpr (fun index : JetIndex order =>
    fieldExtension_ae (CellValues dimension) domain measurable (jet.val index))
  filter_upwards [represented] with point representedAt
  intro index cell
  change fieldExtension (CellValues dimension) domain measurable (jet.val index) point cell = _
  rw [representedAt index]
  by_cases inside : point ∈ domain
  · simp only [Set.indicator_of_mem inside, if_pos inside]
  · simp only [Set.indicator_of_notMem inside, if_neg inside, lp.coeFn_zero, Pi.zero_apply]

theorem restriction_extendJet (dimension order : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order domain exponent)
    (supported : TupleSupported dimension order domain support jet.val) :
    Restriction.restriction dimension order (Set.subset_univ domain) MeasurableSet.univ exponent
        (extendJet dimension order domain support measurable localizer exponent jet supported) = jet := by
  apply jet_eq
  intro index
  exact restriction_extension (CellValues dimension) domain measurable (jet.val index)

theorem extendJet_independent (dimension order : ℕ) (domain firstSupport secondSupport : Set Spatial)
    (measurable : MeasurableSet domain) (firstLocalizer : TestLocalizer domain firstSupport)
    (secondLocalizer : TestLocalizer domain secondSupport) (exponent : JetIndex order → ℕ)
    (jet : WJet dimension order domain exponent)
    (firstSupported : TupleSupported dimension order domain firstSupport jet.val)
    (secondSupported : TupleSupported dimension order domain secondSupport jet.val) :
    extendJet dimension order domain firstSupport measurable firstLocalizer exponent jet firstSupported =
      extendJet dimension order domain secondSupport measurable secondLocalizer exponent jet secondSupported := rfl

end Grad.WeightedJets.ZeroExtension
