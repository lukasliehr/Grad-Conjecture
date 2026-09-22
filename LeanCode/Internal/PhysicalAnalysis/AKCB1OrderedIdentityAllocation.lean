import AKAA22ActualFullCellFirstDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ContDiff Topology
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.RepresentedKernel
open Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct
open Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

theorem startupOrdered_chain_identity {Parameter : Type*} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    {rank : ℕ} (word : Word rank) (selected : Finset (Fin rank))
    (target : Word selectedᶜ.card) (parameter : Parameter)
    (identity : data.orthogonal parameter = LinearIsometryEquiv.refl ℝ _) :
    chainProduct data word selected target parameter =
      if target = subword word selectedᶜ then 1 else 0 := by
  rw [chainProduct,chainFactor_eq,identity]
  change (∏ position, Grad.PDEBootstrap.spatialDirection
    (subword word selectedᶜ position) (target position)) = _
  by_cases same : target = subword word selectedᶜ
  · subst target
    simp [Grad.PDEBootstrap.spatialDirection]
  · rw [if_neg same]
    obtain ⟨position,different⟩ := Function.ne_iff.mp same
    apply Finset.prod_eq_zero (Finset.mem_univ position)
    simp [Grad.PDEBootstrap.spatialDirection,Ne.symm different]

/-- The identity spatial pullback retains exactly the complementary
ordered derivative for every selected set, at arbitrary spatial order. -/
theorem startupOrdered_candidate {Parameter : Type*} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension order rank weight : ℕ}
    (data : RawKernelData measure inputDimension outputDimension openUnitDisk)
    (reference : Parameter) (identity : ∀ parameter, data.orthogonal parameter = LinearIsometryEquiv.refl ℝ _)
    (word : Word rank) (bound : rank ≤ order)
    (field : Grad.WeightedJets.GraphGrade inputDimension order weight openUnitDisk) :
    (∑ selected : Finset (Fin rank), ∑ target : Word selectedᶜ.card,
      operator (allocatedData data word selected target) (0,0) 0
        (inputDerivative inputDimension order rank weight openUnitDisk bound field selected target)) =
    ∑ selected : Finset (Fin rank), operator data (selectedIndex word selected) 0
      (inputDerivative inputDimension order rank weight openUnitDisk bound field selected (subword word selectedᶜ)) := by
  have constant : ∀ parameter, data.orthogonal parameter = data.orthogonal reference :=
    fun parameter => (identity parameter).trans (identity reference).symm
  simp_rw [startupAllocated_operator data reference constant]
  apply Finset.sum_congr rfl
  intro selected _
  change (∑ target : Word selectedᶜ.card,
    (chainProduct data word selected target reference : ℂ) •
      operator data (selectedIndex word selected) 0
        (inputDerivative inputDimension order rank weight openUnitDisk bound field selected target)) = _
  simp_rw [startupOrdered_chain_identity data word selected _ reference (identity reference)]
  rw [Fintype.sum_eq_single (subword word selectedᶜ)]
  · rw [if_pos rfl,Complex.ofReal_one,one_smul]
  · intro target different
    rw [if_neg different,Complex.ofReal_zero,zero_smul]

theorem startupSingleEntry_orderedWeak {inputDimension outputDimension order rank weight : ℕ}
    (jet : SmoothOperatorJet inputDimension outputDimension) (outputCell inputCell : ℤ)
    (word : Word rank) (bound : rank ≤ order)
    (field : Grad.WeightedJets.GraphGrade inputDimension order weight openUnitDisk) :
    HasWeakOrderedDerivative outputDimension openUnitDisk rank word
      (operator (startupSingleEntryData jet outputCell inputCell) (0,0) 0
        (Grad.WeightedJets.base inputDimension order openUnitDisk (fun _ => weight) field))
      (∑ selected : Finset (Fin rank),
        operator (startupSingleEntryData jet outputCell inputCell) (selectedIndex word selected) 0
          (inputDerivative inputDimension order rank weight openUnitDisk bound field selected (subword word selectedᶜ))) := by
  have weak := startupSingleEntry_weak jet outputCell inputCell word bound field
  rw [startupOrdered_candidate (startupSingleEntryData jet outputCell inputCell) (0 : ℝ) (fun _ => rfl)] at weak
  exact weak

end Grad.CartesianStartup
