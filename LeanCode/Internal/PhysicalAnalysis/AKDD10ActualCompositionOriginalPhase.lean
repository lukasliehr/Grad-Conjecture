import AKDD9SameGaugeReconstructionEuler

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularRadialSmoothness Grad.AnnularKernelL2
open Grad.GaugeCoefficients.Physical.Allocation

/-- Phase differentiation spends displacement rank jointly with the exact
coefficient Euler rank. The constant is uniform over every closed collar. -/
theorem OriginalEulerMoments.conjugated {parameters : PhaseParameters} {L compact : ℝ} {source target : ℕ}
    {kernels : (state : AnnularReconstructionState parameters L compact) → ℕ →
      (radius : RadialPoint) → RadialKernel parameters radius source target}
    (moments : OriginalEulerMoments parameters L compact kernels) :
    ∀ rank moment, ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (state : AnnularReconstructionState parameters L compact),
    physicalBudget parameters state.val.field state.val.rho state.val.epsilon 10 ≤ 1 →
    ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1),
    KernelEulerDerivativeTower parameters lower positive bounded.le (kernels state) →
    ∀ (radius : RadialPoint), radius.val ∈ Icc lower 1 → ∀ inputs : (ℤ × ℤ) → (ℤ × ℤ),
    let coefficient := fun point => (kernels state 0 (collarRadius lower positive bounded.le point)).entry
    Summable (fun shift : ℤ × ℤ => Grad.AnnularVariational.annularFrequency shift.1 shift.2^moment *
      ‖actualClosedConjugatedEulerEntry parameters (Icc lower 1) coefficient rank radius.val shift (inputs shift)‖) ∧
    (∑' shift : ℤ × ℤ, Grad.AnnularVariational.annularFrequency shift.1 shift.2^moment *
      ‖actualClosedConjugatedEulerEntry parameters (Icc lower 1) coefficient rank radius.val shift (inputs shift)‖) ≤
      constant*(1+physicalBudget parameters state.val.field state.val.rho state.val.epsilon (10+(rank+moment))) := by
  choose constants nonnegative bounds using moments
  intro rank moment
  let constant := eulerAllocationSum (fun first second => positiveEulerRatioConstant parameters first *
    constants second (moment+first)) (eulerLeibnizTerms rank)
  refine ⟨constant,eulerAllocationSum_nonnegative _ (fun first second => mul_nonneg
    (zero_le_one.trans (positiveEulerRatioConstant_one_le parameters first)) (nonnegative second (moment+first))) _,?_⟩
  intro state low lower positive bounded tower radius inside inputs
  have allocated := actualClosedEulerDisplacementMoment_allocated parameters lower positive bounded
    (kernels state) (tower.entry parameters lower positive bounded.le (kernels state)) radius inside rank moment inputs
  refine ⟨allocated.1,allocated.2.trans ?_⟩
  let size := 1+physicalBudget parameters state.val.field state.val.rho state.val.epsilon (10+(rank+moment))
  have paid : eulerAllocationSum (fun first second => positiveEulerRatioConstant parameters first *
      fullKernelMoment (radialKernelParameters parameters radius) (moment+first) (kernels state second radius)) (eulerLeibnizTerms rank) ≤
      eulerAllocationSum (fun first second => size*(positiveEulerRatioConstant parameters first *
        constants second (moment+first))) (eulerLeibnizTerms rank) := by
    apply eulerAllocationSum_mono
    intro term member
    have degree := eulerLeibnizTerms_rank rank term member
    have actual := bounds term.2 (moment+term.1) state low radius
    rw [show 10+(term.2+(moment+term.1)) = 10+(rank+moment) by omega] at actual
    exact (mul_le_mul_of_nonneg_left actual
      (zero_le_one.trans (positiveEulerRatioConstant_one_le parameters term.1))).trans_eq (by dsimp only [size]; ring)
  apply paid.trans_eq
  rw [← eulerAllocationSum_mul_left]
  exact mul_comm _ _

/-- Genuine Euler derivatives of the SAME original phase-conjugated Q,
with both all-cell row and column Schur selectors and one high budget. -/
theorem originalGaugeQConjugatedEuler_oneHigh (parameters : PhaseParameters) (L compact : ℝ)
    (rank moment : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (state : AnnularReconstructionState parameters L compact),
    physicalBudget parameters state.val.field state.val.rho state.val.epsilon 10 ≤ 1 →
    ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
      (radius : RadialPoint), radius.val ∈ Icc lower 1 → ∀ inputs : (ℤ × ℤ) → (ℤ × ℤ),
    let coefficient := fun point => (radialGaugeQKernel parameters L compact state.val
      (collarRadius lower positive bounded.le point) state.gaugeSmall).entry
    Summable (fun shift : ℤ × ℤ => Grad.AnnularVariational.annularFrequency shift.1 shift.2^moment *
      ‖actualClosedConjugatedEulerEntry parameters (Icc lower 1) coefficient rank radius.val shift (inputs shift)‖) ∧
    (∑' shift : ℤ × ℤ, Grad.AnnularVariational.annularFrequency shift.1 shift.2^moment *
      ‖actualClosedConjugatedEulerEntry parameters (Icc lower 1) coefficient rank radius.val shift (inputs shift)‖) ≤
      constant*(1+physicalBudget parameters state.val.field state.val.rho state.val.epsilon (10+(rank+moment))) := by
  obtain ⟨constant,nonnegative,bound⟩ := (originalGaugeQEulerKernel_originalMoments parameters L compact).conjugated rank moment
  refine ⟨constant,nonnegative,?_⟩
  intro state low lower positive bounded radius inside inputs
  have actual := bound state low lower positive bounded
    (originalGaugeQEulerKernel_derivativeTower parameters L compact state lower positive bounded) radius inside inputs
  have same : (fun point => (originalGaugeQEulerKernel parameters L compact state 0 (collarRadius lower positive bounded.le point)).entry) =
      (fun point => (radialGaugeQKernel parameters L compact state.val (collarRadius lower positive bounded.le point) state.gaugeSmall).entry) := by
    funext point
    rw [originalGaugeQEulerKernel_zero]
  dsimp only at actual
  rw [same] at actual
  exact actual

end Grad.OriginalCartesianTameEstimate
