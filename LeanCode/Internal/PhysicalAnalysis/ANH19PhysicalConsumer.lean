import ANH18WeakSolve

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory

namespace Grad.CircularHighWeak
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.GenericCarriers

attribute [local instance] circlePeriodPositive

/-- The completed form is exactly the bulk and boundary integrals in AN18,
with ordinary disk area and ordinary circle arclength. -/
theorem robinValue_integral (parameter : ℝ) (field test : highDiskGrade) :
    robinValue parameter field test =
      (∫ point in openUnitDisk, inner ℂ (highGradX test point) (highGradX field point)) +
      (∫ point in openUnitDisk, inner ℂ (highGradY test point) (highGradY field point)) +
      (parameter ^ 2 : ℝ) *
        (∫ point in openUnitDisk, inner ℂ (highDiskBulk test point) (diskB (highDiskBulk field) point)) +
      2 * (∫ angle : CellCircle, inner ℂ (robinTrace test angle) (robinTrace field angle)) := by
  simp only [robinValue, L2.inner_def]

theorem weakSolution_energy_coercivity (parameter : ℝ) (field : highDiskGrade) :
    (1 / 2 : ℝ) * ‖energyFromDisk field‖ ^ 2 ≤ robinForm parameter field field := by
  have energy : ‖energyFromDisk field‖ ^ 2 = ‖highDiskBulk field‖ ^ 2 +
      ‖highGradX field‖ ^ 2 + ‖highGradY field‖ ^ 2 + ‖robinTrace field‖ ^ 2 := energy_norm_sq field
  have diagonal := robinForm_diagonal parameter field
  have poincare : 9 * ‖highDiskBulk field‖ ^ 2 ≤ ‖highGradX field‖ ^ 2 + ‖highGradY field‖ ^ 2 :=
    highDisk_poincare field
  have positive := mul_nonneg (sq_nonneg parameter) (diskB_nonnegative (highDiskBulk field))
  nlinarith only [energy, diagonal, poincare, positive, sq_nonneg ‖robinTrace field‖,
    sq_nonneg ‖highDiskBulk field‖]

/-- The same solution has the exact U4 H1-plus-boundary norm bound. -/
theorem weakSolution_energy_bound (parameter : ℝ) (source : highDiskL2) :
    ‖energyFromDisk (weakSolution parameter source)‖ ≤ 2 * ‖source‖ := by
  have coercive := (weakSolution_energy_coercivity parameter (weakSolution parameter source)).trans_eq
    (weakSolution_real parameter source (weakSolution parameter source))
  have cauchy := real_inner_le_norm source.val (highDiskBulk (weakSolution parameter source))
  have bulk := (highBulk_norm_le (weakSolution parameter source)).trans
    (energy_H1_lower (weakSolution parameter source))
  have bound := coercive.trans (cauchy.trans (mul_le_mul_of_nonneg_left bulk (norm_nonneg source.val)))
  change (1 / 2 : ℝ) * ‖energyFromDisk (weakSolution parameter source)‖ ^ 2 ≤
    ‖source‖ * ‖energyFromDisk (weakSolution parameter source)‖ at bound
  nlinarith only [bound, norm_nonneg (energyFromDisk (weakSolution parameter source)), norm_nonneg source]

/-- Dependency-ready AN18: every real parameter and every actual high L2
source admit exactly one weak high solution, with a uniform full-disk H1
bound and the literal complex Robin form. -/
theorem actualHighRobinWeakSolve (parameter : ℝ) (source : highDiskL2) :
    (∃! field : highDiskGrade,
      ∀ test : highDiskGrade, robinValue parameter field test =
        inner ℂ (highDiskBulk test) source.val) ∧
    ‖highRobinWeakInverse parameter source‖ ≤ 2 * ‖source‖ ∧
    ‖energyFromDisk (highRobinWeakInverse parameter source)‖ ≤ 2 * ‖source‖ := by
  refine ⟨⟨weakSolution parameter source, weakSolution_equation parameter source,
    fun field equation => weakSolution_unique parameter source field equation⟩,
    weakSolution_bound parameter source, weakSolution_energy_bound parameter source⟩

/-- Immediate universal downstream consumer uses the constructed operator,
its literal bulk/boundary integral equation, uniqueness and uniform bound. -/
theorem actualHighRobinWeakConsumer (parameter : ℝ) (source : highDiskL2) :
    let field := highRobinWeakInverse parameter source
    (∀ test : highDiskGrade,
      (∫ point in openUnitDisk, inner ℂ (highGradX test point) (highGradX field point)) +
      (∫ point in openUnitDisk, inner ℂ (highGradY test point) (highGradY field point)) +
      (parameter ^ 2 : ℝ) *
        (∫ point in openUnitDisk, inner ℂ (highDiskBulk test point) (diskB (highDiskBulk field) point)) +
      2 * (∫ angle : CellCircle, inner ℂ (robinTrace test angle) (robinTrace field angle)) =
      ∫ point in openUnitDisk, inner ℂ (highDiskBulk test point) (source.val point)) ∧
    ‖field‖ ≤ 2 * ‖source‖ := by
  constructor
  · intro test
    exact (robinValue_integral parameter (highRobinWeakInverse parameter source) test).symm.trans
      ((highRobinWeakInverse_equation parameter source test).trans (by rfl))
  · exact weakSolution_bound parameter source

end Grad.CircularHighWeak
