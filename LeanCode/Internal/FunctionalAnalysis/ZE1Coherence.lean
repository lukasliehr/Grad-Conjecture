import ZE1Maps

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue CellValues FieldL2)
open scoped BigOperators Topology

namespace Grad.WeightedJets.ZeroExtension

set_option maxHeartbeats 1200000

theorem inverseField_supported (dimension : ℕ) (domain support : Set Spatial) (power : ℕ)
    (field : FieldL2 dimension domain) (supported : SupportedField (CellValues dimension) domain support field) :
    SupportedField (CellValues dimension) domain support
      (Grad.CellWeights.inverseFieldCLM dimension domain power field) := by
  filter_upwards [supported, Grad.CellWeights.inverseFieldCLM_ae dimension domain power field]
    with point zeroAt represented
  intro outside
  rw [represented, zeroAt outside, map_zero]

theorem inclusion_supported (dimension lower higher : ℕ) (domain support : Set Spatial)
    (gap : ℕ) (bound : lower ≤ higher) (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ)
    (compatible : Inclusions.Compatible bound gap source target)
    (jet : WJet dimension higher domain source)
    (supported : TupleSupported dimension higher domain support jet.val) :
    TupleSupported dimension lower domain support
      (Inclusions.inclusion dimension lower higher domain gap bound source target compatible jet).val := by
  intro index
  exact inverseField_supported dimension domain support gap (jet.val (Inclusions.indexInclusion bound index))
    (supported (Inclusions.indexInclusion bound index))

theorem extendJet_inclusion (dimension lower higher : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (gap : ℕ) (bound : lower ≤ higher) (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ)
    (compatible : Inclusions.Compatible bound gap source target)
    (jet : WJet dimension higher domain source)
    (supported : TupleSupported dimension higher domain support jet.val) :
    extendJet dimension lower domain support measurable localizer target
        (Inclusions.inclusion dimension lower higher domain gap bound source target compatible jet)
        (inclusion_supported dimension lower higher domain support gap bound source target compatible jet supported) =
      Inclusions.inclusion dimension lower higher Set.univ gap bound source target compatible
        (extendJet dimension higher domain support measurable localizer source jet supported) := by
  apply jet_eq
  intro index
  exact fieldExtension_inverse dimension domain measurable gap (jet.val (Inclusions.indexInclusion bound index))

theorem extendJet_weak_integral (dimension order : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order domain exponent)
    (supported : TupleSupported dimension order domain support jet.val)
    (index : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension)
    (test : TestFunction Set.univ) :
    (∫ point in (Set.univ : Set Spatial), test.toFun point •
      inner ℂ vector (fieldExtension (CellValues dimension) domain measurable
        (Realization.recoveredDerivative dimension order domain exponent index jet) point cell)) =
      (-1 : ℂ) ^ degree index *
        ∫ point in (Set.univ : Set Spatial),
          Grad.WeakTesting.orderedTestDerivative (degree index) (derivativeWord index) test.toFun point •
            inner ℂ vector (fieldExtension (CellValues dimension) domain measurable
              (base dimension order domain exponent jet) point cell) := by
  rw [← extendJet_recoveredDerivative dimension order domain support measurable localizer exponent jet supported index,
    ← extendJet_base dimension order domain support measurable localizer exponent jet supported]
  exact Realization.recoveredDerivative_integral dimension order Set.univ exponent index
    (extendJet dimension order domain support measurable localizer exponent jet supported) cell vector test

theorem jetExtension_tendsto (dimension order : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (exponent : JetIndex order → ℕ) {Index : Type*} {filter : Filter Index}
    {approximants : Index → supportedJetSubmodule dimension order domain support exponent}
    {jet : supportedJetSubmodule dimension order domain support exponent}
    (convergence : Filter.Tendsto approximants filter (𝓝 jet)) :
    Filter.Tendsto
      (fun index => jetExtension dimension order domain support measurable localizer exponent (approximants index))
      filter (𝓝 (jetExtension dimension order domain support measurable localizer exponent jet)) :=
  ((jetExtension dimension order domain support measurable localizer exponent).continuous.tendsto jet).comp convergence

theorem extendJet_norm_sq (dimension order : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order domain exponent)
    (supported : TupleSupported dimension order domain support jet.val) :
    ‖extendJet dimension order domain support measurable localizer exponent jet supported‖ ^ 2 =
      ∑ index : JetIndex order, ‖jet.val index‖ ^ 2 := by
  rw [extendJet_norm, jet_norm_sq]

theorem graphGrade_consumer (dimension order weight : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (jet : GraphGrade dimension order weight domain)
    (supported : TupleSupported dimension order domain support jet.val) :
    ‖extendJet dimension order domain support measurable localizer (fun _ => weight) jet supported‖ = ‖jet‖ :=
  extendJet_norm dimension order domain support measurable localizer _ jet supported

theorem mixed_consumer (dimension grade : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (jet : Mixed dimension grade domain)
    (supported : TupleSupported dimension grade domain support jet.val) :
    ‖extendJet dimension grade domain support measurable localizer (fun index => grade - degree index)
      jet supported‖ = ‖jet‖ :=
  extendJet_norm dimension grade domain support measurable localizer _ jet supported

theorem zeroDimension (order : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (exponent : JetIndex order → ℕ) :
    ‖(jetExtension 0 order domain support measurable localizer exponent).toContinuousLinearMap‖ ≤ 1 :=
  jetExtension_opNorm_le 0 order domain support measurable localizer exponent

theorem zeroOrder (dimension : ℕ) (domain support : Set Spatial)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (exponent : JetIndex 0 → ℕ) (jet : WJet dimension 0 domain exponent)
    (supported : TupleSupported dimension 0 domain support jet.val) :
    base dimension 0 Set.univ exponent (extendJet dimension 0 domain support measurable localizer exponent jet supported) =
      fieldExtension (CellValues dimension) domain measurable (base dimension 0 domain exponent jet) :=
  extendJet_base dimension 0 domain support measurable localizer exponent jet supported

end Grad.WeightedJets.ZeroExtension

