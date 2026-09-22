import QYP9PhysicalForward

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 600000

open scoped BigOperators ContDiff

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.Q24Realization Grad.NonlinearQuotientBounds Grad.SmoothForward

/-- Pure state variation, with exactly zero seed and curvature directions. -/
def physicalStateDirection (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    stateRange parameters reference insideR grade large →L[ℝ]
      RealMixedAmbient parameters reference insideR grade large :=
  (realMixedJointDirection parameters reference insideR grade large).comp
    (stateDirection parameters reference insideR grade large)

theorem physicalStateDirection_norm (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (direction : stateRange parameters reference insideR grade large) :
    ‖physicalStateDirection parameters reference insideR grade large direction‖ = ‖direction‖ := by
  rw [WithLp.prod_norm_eq_of_L1]
  change ‖(0 : SeedL1)‖ + ‖stateDirection parameters reference insideR grade large direction‖ = _
  rw [norm_zero, zero_add, stateDirection_norm]

theorem physicalStateDirection_lowering {lower upper : ℕ} (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (direction : stateRange parameters reference insideR upper (large.trans ordered)) :
    realMixedLowering parameters reference insideR large ordered
      (physicalStateDirection parameters reference insideR upper (large.trans ordered) direction) =
    physicalStateDirection parameters reference insideR lower large
      (stateLowering parameters reference insideR large ordered direction) := rfl

theorem physicalStateDirection_core (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (direction : stateSmoothRange parameters reference insideR) :
    physicalStateDirection parameters reference insideR grade large
      (stateSmoothEmbedding parameters reference insideR grade large direction) =
    realMixedCoreEmbed parameters reference insideR grade large (0, 0, direction) := rfl

theorem physicalStateDirection_oneHigh (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ)
    (base : RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (direction : stateRange parameters reference insideR (grade + 6) (realHighLarge grade)) :
    realMixedCompletedOneHigh parameters reference insideR grade 1 base
      (fun _ => physicalStateDirection parameters reference insideR (grade + 6) (realHighLarge grade) direction) =
    (1 + ‖base.ofLp.2.ofLp.2‖) *
      ‖stateLowering parameters reference insideR realLowLarge (realLowLeHigh grade) direction‖ + ‖direction‖ := by
  have empty : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
  simp only [realMixedCompletedOneHigh, Fin.prod_univ_one, Fin.sum_univ_one, empty,
    Finset.prod_empty, mul_one]
  rw [physicalStateDirection_lowering, physicalStateDirection_norm, physicalStateDirection_norm]

theorem actualPhysicalSmoothForward_tame_of_mixed (parameters : PhaseParameters) (cellLength epsilon : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (mixedEstimate : PhysicalMixedDerivativeEstimate parameters cellLength reference insideR)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (bound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : stateSmoothRange parameters reference insideR),
      ChartAxisCondition (smoothingChartCore parameters base.val) →
      ‖stateSmoothEmbedding parameters reference insideR 4 realLowLarge base‖ ≤ bound →
      ∀ direction : stateRange parameters reference insideR (grade + 6) (realHighLarge grade),
      ‖actualPhysicalSmoothForward parameters cellLength reference insideR seed grade large (epsilon, base) direction‖ ≤
      constant * ((1 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) base‖) *
        ‖stateLowering parameters reference insideR realLowLarge (realLowLeHigh grade) direction‖ + ‖direction‖) := by
  obtain ⟨constant, nonneg, estimate⟩ := mixedEstimate grade large 1 {seed} (isCompact_singleton)
    (by simpa only [Set.singleton_subset_iff] using insideS) |epsilon| bound
  refine ⟨constant, nonneg, fun base axis bounded direction => ?_⟩
  let point := realMixedCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) (seed, epsilon, base)
  have inside := (realMixedDomain_core_iff parameters reference insideR (grade + 6)
    (realHighLarge grade) (seed, epsilon, base)).2 ⟨insideS, axis⟩
  have low : ‖stateLowering parameters reference insideR realLowLarge (realLowLeHigh grade)
      point.ofLp.2.ofLp.2‖ ≤ bound := by
    change ‖stateLowering parameters reference insideR realLowLarge (realLowLeHigh grade)
      (stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) base)‖ ≤ bound
    rw [stateLowering_core]
    exact bounded
  have result := estimate point
    (fun _ => physicalStateDirection parameters reference insideR (grade + 6) (realHighLarge grade) direction)
    (show seed ∈ ({seed} : Set Seed.Parameters) from Set.mem_singleton seed)
    (show ‖epsilon‖ ≤ |epsilon| by rw [Real.norm_eq_abs]) inside low
  rw [iteratedFDeriv_one_apply, physicalStateDirection_oneHigh] at result
  rw [actualPhysicalSmoothForward_mixed parameters cellLength reference insideR seed insideS grade large (epsilon, base) axis]
  exact result

end Grad.PhysicalCoordinates
