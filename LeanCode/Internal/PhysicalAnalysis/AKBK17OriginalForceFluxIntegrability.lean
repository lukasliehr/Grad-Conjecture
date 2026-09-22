import AKBK6SameCellForceFlux

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
namespace Grad.ActualCartesianWeakEquations
open Grad.ClosedJets Grad.PDEBootstrap Grad.ActualSmoothPhysicalField Grad.PhysicalAxisEquation

private theorem originalWeighted_sub_integrable {E : Type*} [NormedAddCommGroup E]
    (first second : Spatial → E) (firstIntegrable : IntegrableOn first openUnitDisk)
    (secondIntegrable : IntegrableOn second openUnitDisk)
    (firstWeighted : IntegrableOn (fun point => ‖point‖⁻¹ * ‖first point‖) openUnitDisk)
    (secondWeighted : IntegrableOn (fun point => ‖point‖⁻¹ * ‖second point‖) openUnitDisk) :
    IntegrableOn (fun point => ‖point‖⁻¹ * ‖first point - second point‖) openUnitDisk := by
  apply (firstWeighted.add secondWeighted).mono'
    (measurable_id.norm.inv.aestronglyMeasurable.mul (firstIntegrable.sub secondIntegrable).aestronglyMeasurable.norm)
  apply Eventually.of_forall
  intro point
  change ‖‖point‖⁻¹ * ‖first point - second point‖‖ ≤ ‖point‖⁻¹ * ‖first point‖ + ‖point‖⁻¹ * ‖second point‖
  rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)),← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr (norm_nonneg _))

/-- The original force flux and its norm/r are integrable using only the
existing native Xi and covariant bounds, with no derivative estimate. -/
theorem originalForceFlux_integrable_pair (xi : Spatial → ℂ) (covariant : Spatial → ComplexEuclidean 2)
    (xiIntegrable : IntegrableOn xi openUnitDisk)
    (xiWeighted : IntegrableOn (fun point => ‖point‖⁻¹ * ‖xi point‖) openUnitDisk)
    (covariantIntegrable : IntegrableOn covariant openUnitDisk)
    (covariantWeighted : IntegrableOn (fun point => ‖point‖⁻¹ * ‖covariant point‖) openUnitDisk)
    (coordinate direction : Fin 2) :
    IntegrableOn (originalForceFlux xi covariant coordinate direction) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖originalForceFlux xi covariant coordinate direction point‖) openUnitDisk := by
  let projection := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) coordinate).restrictScalars ℝ
  have component := boundedPhysicalFlux_integrable_pair openUnitDisk covariant covariantIntegrable covariantWeighted
    (fun _ => projection) aestronglyMeasurable_const ‖projection‖ (Eventually.of_forall (fun _ => le_rfl))
  have transported := angularTransportFlux_integrable_pair (fun point => covariant point coordinate) component.1 component.2 direction
  have scalar : IntegrableOn (fun point => if direction = coordinate then xi point else 0) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖if direction = coordinate then xi point else 0‖) openUnitDisk := by
    by_cases equal : direction = coordinate
    · simpa only [if_pos equal] using And.intro xiIntegrable xiWeighted
    · simp only [if_neg equal,norm_zero,mul_zero]
      exact ⟨integrable_zero _ _ _,integrable_zero _ _ _⟩
  exact ⟨scalar.1.sub transported.1,
    originalWeighted_sub_integrable _ _ scalar.1 transported.1 scalar.2 transported.2⟩

end Grad.ActualCartesianWeakEquations
