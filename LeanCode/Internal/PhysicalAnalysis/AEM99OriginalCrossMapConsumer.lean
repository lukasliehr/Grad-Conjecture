import AEM24ExactGraphNativeCrossEmbedding

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.ActualBoundaryPrimitives Grad.AnnularCurrentSource Grad.GaugeCoefficients.Physical.Allocation

/-- The boundary primitive uses the same actual radial reconstruction at
r=1; the seven normalization factors are exactly the identity there. -/
theorem originalCrossMaps_outer_reconstruction (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact) :
    SameKernelEntries
      (radialNormalizedCovariantKernel parameters length compact state.val.val outerRadialPoint state.val.property)
      state.boundaryState.covariant ∧
    SameKernelEntries
      (radialNormalizedRotatedCovariantKernel parameters length compact state.val.val outerRadialPoint state.val.property)
      state.boundaryState.rotatedCovariant ∧
    SameKernelEntries (radialSevenSlotKernel parameters outerRadialPoint) (fullIdentityKernel parameters 7) :=
  ⟨radialNormalizedCovariantKernel_one parameters length compact state.val.val state.val.property,
    radialNormalizedRotatedCovariantKernel_one parameters length compact state.val.val state.val.property,
    radialSevenSlotKernel_one parameters⟩

/-- BF16/BF18: actual physical cross maps between the original complete low
energy graph, literal W×Domega, and the exact independent data carriers.
The common B8 coefficient is chosen before every collar and physical state. -/
theorem originalCrossMaps_uniform (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
      (state : RetainedInverseState parameters length compact),
      ‖lowToHighCross parameters lower length compact lengthPositive positive lowerHalf state‖ ≤
        constant * physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ∧
      ‖highToLowCross parameters lower length compact lengthPositive positive (lowerHalf.trans (by norm_num)) state‖ ≤
        constant * physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 := by
  let first := lowToHighErrorConstant parameters length compact
  let second := highToLowErrorConstant parameters length compact
  have firstNonnegative : 0 ≤ first := lowToHighErrorConstant_nonnegative parameters length compact lengthPositive
  have secondNonnegative : 0 ≤ second := highToLowErrorConstant_nonnegative parameters length compact
  refine ⟨first + second, add_nonneg firstNonnegative secondNonnegative, ?_⟩
  intro lower positive lowerHalf state
  have budget := physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8
  constructor
  · apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (add_nonneg firstNonnegative secondNonnegative) budget)
    intro field
    exact (lowToHighCross_B8 parameters lower length compact lengthPositive positive lowerHalf state field).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right secondNonnegative) budget) (norm_nonneg field))
  · apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (add_nonneg firstNonnegative secondNonnegative) budget)
    intro field
    exact (highToLowCross_B8 parameters lower length compact lengthPositive positive (lowerHalf.trans (by norm_num)) state field).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left firstNonnegative) budget) (norm_nonneg field))

/-- Immediate genuine consumer: the low-to-high output is an admissible
AEK source-graph datum with every unused prescribed source and g exactly zero;
the reverse map has the original zero incoming coordinate. -/
theorem originalCrossMaps_exact_data (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (state : RetainedInverseState parameters length compact)
    (lowField : lowEnergyGraph lower length positive) (highField : CrossHighSpace lower length positive lengthPositive) :
    let data := (lowToHighCross parameters lower length compact lengthPositive positive lowerHalf state lowField).toGraphKnown parameters lower
    data.weighted 0 = 0 ∧ data.weighted 1 = 0 ∧ data.weighted 2 = 0 ∧ data.auxiliary 0 = 0 ∧ data.graphs = 0 ∧
    data.innerValue = 0 ∧
    data.datum = lowToHighBoundaryCross parameters lower length compact lengthPositive positive lowerHalf state lowField ∧
    (highToLowCross parameters lower length compact lengthPositive positive (lowerHalf.trans (by norm_num)) state highField).ofLp.2 = 0 ∧
    WeightedGraphCompatibility parameters lower 0 data.graphs data.weighted := by
  dsimp only
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    crossKnownWeighted_graph parameters lower (lowToHighCross parameters lower length compact lengthPositive positive lowerHalf state lowField)⟩

end Grad.AnnularCrossMaps
