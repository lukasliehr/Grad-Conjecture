import RKWD1CoreIBP
import RKWD1Closure

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open Grad.RepresentedKernel.SpatialProduct
open Grad.SpatialDilation (disk)
open scoped BigOperators ContDiff Topology

universe parameterUniverse

namespace Grad.RepresentedKernel.WeakDerivatives

def derivativeCandidateCLM
    {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension order rank weight : ℕ} {radius : ℝ}
    (_data : RawKernelData measure inputDimension outputDimension (disk radius))
    (_word : Word rank) (bound : rank ≤ order)
    (family : AllocatedFamily measure inputDimension outputDimension (disk radius) rank) :
    Grad.WeightedJets.GraphGrade inputDimension order weight (disk radius) →L[ℂ]
      FieldL2 outputDimension (disk radius) :=
  ∑ selected : Finset (Fin rank), ∑ target : Word (selectedᶜ).card,
    (operator (family selected target) (0, 0) 0).comp
      ((tensorProjection (FieldL2 inputDimension (disk radius)) (selectedᶜ).card target).comp
        (Grad.WeightedJets.Ordered.orderedDerivative inputDimension order (selectedᶜ).card
          (disk radius) (fun _ => weight) (by
            have complementBound : (selectedᶜ).card ≤ rank := by
              simpa only [Fintype.card_fin] using Finset.card_le_univ selectedᶜ
            exact complementBound.trans bound)))

theorem derivativeCandidateCLM_apply
    {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension order rank weight : ℕ} {radius : ℝ}
    (data : RawKernelData measure inputDimension outputDimension (disk radius))
    (word : Word rank) (bound : rank ≤ order)
    (family : AllocatedFamily measure inputDimension outputDimension (disk radius) rank)
    (jet : Grad.WeightedJets.GraphGrade inputDimension order weight (disk radius)) :
    derivativeCandidateCLM data word bound family jet =
      derivativeCandidate data word bound jet family := by
  rw [derivativeCandidateCLM, derivativeCandidate]
  simp only [sum_apply, ContinuousLinearMap.comp_apply]
  rfl

set_option maxHeartbeats 4000000 in
theorem densityPassage : DensityPassageGoal.{parameterUniverse} := by
  intro Parameter _ measure _ inputDimension outputDimension order rank weight radius positiveRadius
    data word bound family familySpec jet
  let baseField :=
    Grad.WeightedJets.base inputDimension order (disk radius) (fun _ => weight) jet
  let orders : Fin 1 → ℕ := fun _ => order
  let weights : Fin 1 → ℕ := fun _ => weight
  let jets : ∀ index : Fin 1,
      Grad.WeightedJets.GraphGrade inputDimension (orders index) (weights index) (disk radius) :=
    fun _ => jet
  have sameBase : ∀ index : Fin 1,
      Grad.WeightedJets.base inputDimension (orders index) (disk radius)
        (fun _ => weights index) (jets index) = baseField := by
    intro index
    rfl
  obtain ⟨steps, _scaleLimit, _epsilonLimit, _cellGrowth, cores, _fieldLimit,
      approximations⟩ :=
    Grad.SmoothDensity.graph_consumer inputDimension 1 radius positiveRadius orders weights
      baseField jets sameBase
  let approximant (number : ℕ) :
      Grad.WeightedJets.WJet inputDimension order (disk radius) (fun _ => weight) :=
    Grad.SmoothDensity.restrictJet inputDimension radius (.graph order weight)
      (Grad.SmoothDensity.stepJet inputDimension radius positiveRadius (.graph order weight)
        (steps number) jet)
  let function (number : ℕ) : Spatial → CellValues inputDimension :=
    Grad.SmoothDensity.stepFunction inputDimension radius positiveRadius (steps number) baseField
  let cells (number : ℕ) : Finset ℤ :=
    Grad.WeightedJets.CellCutoff.centeredCells (steps number).cellRadius
  have approximantLimit : Filter.Tendsto approximant Filter.atTop (nhds jet) := by
    change Filter.Tendsto (fun number =>
      Grad.SmoothDensity.restrictJet inputDimension radius (.graph order weight)
        (Grad.SmoothDensity.stepJet inputDimension radius positiveRadius (.graph order weight)
          (steps number) jet)) Filter.atTop (nhds jet)
    convert (approximations (0 : Fin 1)).2 using 1
  have coreLaw (number : ℕ) : Grad.SmoothDensity.CoreLaws inputDimension
      (function number) (cells number) := by
    simpa only [function, cells] using cores number
  have realized (number : ℕ) : Grad.SmoothDensity.Realizes inputDimension (disk radius)
      (.graph order weight) (function number) (approximant number) := by
    have univRealized := (approximations (0 : Fin 1)).1 number
    have restricted := Grad.SmoothDensity.realizes_restriction inputDimension
      (Set.subset_univ (disk radius)) MeasurableSet.univ (.graph order weight)
      (function number)
      (Grad.SmoothDensity.stepJet inputDimension radius positiveRadius (.graph order weight)
        (steps number) jet)
      (by simpa only [function, baseField, orders, weights, jets] using univRealized)
    simpa only [approximant, Grad.SmoothDensity.restrictJet] using restricted
  have weak (number : ℕ) :
      Grad.WeakTesting.Commutation.HasWeakOrderedDerivative outputDimension (disk radius) rank word
        (operator data (0, 0) 0
          (Grad.WeightedJets.base inputDimension order (disk radius) (fun _ => weight)
            (approximant number)))
        (derivativeCandidate data word bound (approximant number) family) := by
    apply (Grad.WeakTesting.Commutation.hasWeakOrderedDerivative_iff_integral
      outputDimension (disk radius) rank word _ _).2
    intro output vector test testSmooth testCompact testSupported
    exact coreIBP Parameter measure inputDimension outputDimension order rank weight radius
      positiveRadius data word bound family familySpec (approximant number) (function number)
      (cells number) (coreLaw number) (realized number) output vector test testSmooth testCompact
      testSupported
  have fieldLimit : Filter.Tendsto (fun number => operator data (0, 0) 0
      (Grad.WeightedJets.base inputDimension order (disk radius) (fun _ => weight)
        (approximant number))) Filter.atTop
      (nhds (operator data (0, 0) 0
        (Grad.WeightedJets.base inputDimension order (disk radius) (fun _ => weight) jet))) :=
    ((operator data (0, 0) 0).comp
      (Grad.WeightedJets.base inputDimension order (disk radius) (fun _ => weight))).continuous
        |>.continuousAt.tendsto.comp approximantLimit
  have derivativeLimit : Filter.Tendsto (fun number =>
      derivativeCandidate data word bound (approximant number) family) Filter.atTop
      (nhds (derivativeCandidate data word bound jet family)) := by
    have sourceEquality : (fun number =>
        derivativeCandidate data word bound (approximant number) family) =
        (fun number => derivativeCandidateCLM data word bound family (approximant number)) := by
      funext number
      exact (derivativeCandidateCLM_apply data word bound family (approximant number)).symm
    rw [sourceEquality, ← derivativeCandidateCLM_apply data word bound family jet]
    exact (derivativeCandidateCLM data word bound family).continuous.continuousAt.tendsto.comp
      approximantLimit
  exact closedWeak outputDimension rank (disk radius) word
    (fun number => operator data (0, 0) 0
      (Grad.WeightedJets.base inputDimension order (disk radius) (fun _ => weight)
        (approximant number)))
    (fun number => derivativeCandidate data word bound (approximant number) family)
    (operator data (0, 0) 0
      (Grad.WeightedJets.base inputDimension order (disk radius) (fun _ => weight) jet))
    (derivativeCandidate data word bound jet family) fieldLimit derivativeLimit weak

end Grad.RepresentedKernel.WeakDerivatives
