import AKDH6LiteralPhysicalRadiusFlux

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularRadialSmoothness Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularKernelL2 Grad.AnnularCurrentLow

/-- Original physical rows j,c,rV, with the literal P already inside rV. -/
def physicalRowEulerKernel (parameters : PhaseParameters) (L compact : ℝ)
    (row : Fin 3) : (state : AnnularReconstructionState parameters L compact) →
      ℕ → (radius : RadialPoint) → RadialKernel parameters radius 7 1 :=
  Fin.cases (originalPhysicalFirstRowEulerFamily parameters L compact).kernels
    (Fin.cases (originalPhysicalCEulerFamily parameters L compact).kernels
      (fun _ => (originalPhysicalRVEulerFamily parameters L compact).kernels)) row

theorem physicalRowEulerKernel_zero (parameters : PhaseParameters) (L compact : ℝ)
    (row : Fin 3) (state : RetainedInverseState parameters L compact) (radius : RadialPoint) :
    physicalRowEulerKernel parameters L compact row state.val 0 radius =
      lowPhysicalRowKernel parameters L compact state row radius := by
  fin_cases row
  · exact originalPhysicalFirstRowEulerFamily_same parameters L compact state radius
  · exact originalPhysicalCEulerFamily_same parameters L compact state radius
  · exact originalPhysicalRVEulerFamily_same parameters L compact state radius

theorem physicalRowEulerKernel_derivative (parameters : PhaseParameters) (L compact : ℝ)
    (row : Fin 3) (state : AnnularReconstructionState parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    KernelEulerDerivativeTower parameters lower positive bounded.le
      (physicalRowEulerKernel parameters L compact row state) := by
  fin_cases row
  · exact (originalPhysicalFirstRowEulerFamily parameters L compact).derivative state lower positive bounded
  · exact (originalPhysicalCEulerFamily parameters L compact).derivative state lower positive bounded
  · exact (originalPhysicalRVEulerFamily parameters L compact).derivative state lower positive bounded

theorem physicalRowEulerKernel_moments (parameters : PhaseParameters) (L compact : ℝ)
    (row : Fin 3) : OriginalEulerMoments parameters L compact (physicalRowEulerKernel parameters L compact row) := by
  fin_cases row
  · exact (originalPhysicalFirstRowEulerFamily parameters L compact).moments
  · exact (originalPhysicalCEulerFamily parameters L compact).moments
  · exact (originalPhysicalRVEulerFamily parameters L compact).moments

/-- SR13 for the literal physical rows consumed by the balanced equation.
The derivative is the actual closed-collar Euler derivative; all input
cells, the original phase and one high B_(10+rank+moment) are retained. -/
theorem actualPhysicalRows_originalPhase (parameters : PhaseParameters) (L compact : ℝ)
    (row : Fin 3) (rank moment : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (state : RetainedInverseState parameters L compact),
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
      (radius : RadialPoint), radius.val ∈ Icc lower 1 → ∀ inputs : (ℤ × ℤ) → (ℤ × ℤ),
    let coefficient := fun point =>
      (lowPhysicalRowKernel parameters L compact state row (collarRadius lower positive bounded.le point)).entry
    Summable (fun shift : ℤ × ℤ => Grad.AnnularVariational.annularFrequency shift.1 shift.2^moment *
      ‖actualClosedConjugatedEulerEntry parameters (Icc lower 1) coefficient rank radius.val shift (inputs shift)‖) ∧
    (∑' shift : ℤ × ℤ, Grad.AnnularVariational.annularFrequency shift.1 shift.2^moment *
      ‖actualClosedConjugatedEulerEntry parameters (Icc lower 1) coefficient rank radius.val shift (inputs shift)‖) ≤
      constant*(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+(rank+moment))) := by
  obtain ⟨constant,nonnegative,bound⟩ := (physicalRowEulerKernel_moments parameters L compact row).conjugated rank moment
  refine ⟨constant,nonnegative,?_⟩
  intro state low lower positive bounded radius inside inputs
  have actual := bound state.val low lower positive bounded
    (physicalRowEulerKernel_derivative parameters L compact row state.val lower positive bounded) radius inside inputs
  have same : (fun point => (physicalRowEulerKernel parameters L compact row state.val 0
      (collarRadius lower positive bounded.le point)).entry) =
      (fun point => (lowPhysicalRowKernel parameters L compact state row
        (collarRadius lower positive bounded.le point)).entry) := by
    funext point
    rw [physicalRowEulerKernel_zero]
  dsimp only at actual
  rw [same] at actual
  exact actual

end Grad.OriginalCartesianTameEstimate
