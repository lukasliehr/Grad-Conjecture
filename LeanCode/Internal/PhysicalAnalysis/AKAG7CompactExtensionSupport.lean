import AKAG1CompactWeakSmoothTests

noncomputable section

open MeasureTheory
open Grad.PDEBootstrap

namespace Grad.CartesianStartup

open Grad.WeightedJets Grad.WeightedJets.ZeroExtension

/-- Zero extension preserves the actual compact support of each L2 coordinate. -/
theorem startupFieldExtension_supported
    (dimension : ℕ) (domain support : Set Spatial) (measurable : MeasurableSet domain)
    (field : Grad.GenericCarriers.FieldL2 dimension domain)
    (supported : SupportedField (Grad.GenericCarriers.CellValues dimension) domain support field) :
    SupportedField (Grad.GenericCarriers.CellValues dimension) Set.univ support
      (fieldExtension (Grad.GenericCarriers.CellValues dimension) domain measurable field) := by
  apply ae_restrict_of_ae
  have original : ∀ᵐ point ∂volume, point ∈ domain → point ∉ support → field point = 0 :=
    (ae_restrict_iff' measurable).mp supported
  filter_upwards [fieldExtension_ae (Grad.GenericCarriers.CellValues dimension) domain measurable field,
    original] with point represented zeroAt
  intro outside
  rw [represented]
  by_cases inside : point ∈ domain
  · rw [Set.indicator_of_mem inside]
    exact zeroAt inside outside
  · exact Set.indicator_of_notMem inside _

theorem startupExtendJet_supported
    (dimension order : ℕ) (domain support : Set Spatial) (measurable : MeasurableSet domain)
    (localizer : TestLocalizer domain support) (exponent : JetIndex order → ℕ)
    (field : WJet dimension order domain exponent)
    (supported : TupleSupported dimension order domain support field.val) :
    TupleSupported dimension order Set.univ support
      (extendJet dimension order domain support measurable localizer exponent field supported).val := by
  intro index
  exact startupFieldExtension_supported dimension domain support measurable (field.val index) (supported index)

end Grad.CartesianStartup
