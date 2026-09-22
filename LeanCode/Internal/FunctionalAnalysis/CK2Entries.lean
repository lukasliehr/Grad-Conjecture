import CK2Data
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

noncomputable section

open MeasureTheory MeasureTheory.Measure Grad.PDEBootstrap Grad.GenericCarriers
open scoped BigOperators Topology ENNReal

namespace Grad.RepresentedKernel.Composition.Countable

variable {Outer Inner : Type*} [MeasurableSpace Outer] [MeasurableSpace Inner]
  {outerMeasure : Measure Outer} {innerMeasure : Measure Inner}
  [SigmaFinite outerMeasure] [SigmaFinite innerMeasure]
  {inputDimension middleDimension outputDimension : ℕ} {domain : Set Spatial}
  (outer : Grad.FullCellKernel.L2KernelData outerMeasure middleDimension outputDimension domain)
  (inner : Grad.FullCellKernel.L2KernelData innerMeasure inputDimension middleDimension domain)

theorem pairField_norm_summable (output input : ℤ) (field : DomainL2 (PhysicalValue inputDimension) domain) :
    Summable (fun middle : ℤ => ‖pairOperator outer inner output middle input field‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun middle => (pairOperator outer inner output middle input).le_opNorm field)
    ((pairOperator_norm_summable outer inner output input).mul_right ‖field‖)

theorem combinedEntry_apply (output input : ℤ) (field : DomainL2 (PhysicalValue inputDimension) domain) :
    combinedEntry outer inner output input field = ∑' middle : ℤ, pairOperator outer inner output middle input field :=
  (ContinuousLinearMap.apply ℂ (DomainL2 (PhysicalValue outputDimension) domain) field).map_tsum
    (pairOperator_summable outer inner output input)

theorem composedEntry_eq (output input : ℤ) :
    Grad.FullCellKernel.entry (composedData outer inner) output input = combinedEntry outer inner output input := by
  apply ContinuousLinearMap.ext
  intro field
  rw [combinedEntry_apply]
  apply Lp.ext
  have pairRepresentatives : ∀ᵐ point ∂volume.restrict domain, ∀ middle : ℤ,
      pairOperator outer inner output middle input field point =
        ∫ parameter, pairCoefficient outer inner output middle input (parameter, point)
          (field (pairOrthogonal outer inner parameter point)) ∂outerMeasure.prod innerMeasure :=
    ae_all_iff.mpr (fun middle => pairOperator_ae outer inner output middle input field)
  have sumRepresentative := Lp.coeFn_tsum
    (tsum_enorm_ne_top_iff_summable_norm.mpr (pairField_norm_summable outer inner output input field))
  filter_upwards [entry_ae (composedData outer inner) output input field,
    entry_integrable (composedData outer inner) output input field, pairRepresentatives, sumRepresentative]
    with point represented integrability pairs sumAt
  rw [represented, sumAt, integral_prod _ integrability, integral_countable integrability.integral_prod_left]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  apply tsum_congr
  intro middle
  exact (pairs middle).symm

end Grad.RepresentedKernel.Composition.Countable
