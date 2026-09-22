import QY35RootSeedAllocation
import Q23SeedFamilyGenuine

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 300000

open Filter
open scoped BigOperators Topology

namespace Grad.MixedQuotientComposition

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.NonlinearQuotientBounds
open Grad.Q24Realization

variable {parameters : PhaseParameters}

private theorem rootSeedTerm_genuine
    (seedRule : ∀ (count : ℕ) (base : Input parameters)
      (directions : Fin (count + 1) → Input parameters),
      base.1 ∈ Grad.Constraints.Seed.parameterDomain → ∀ grade,
      Tendsto (fun t : ℝ => originalGradeNorm grade
        (((t : ℂ)⁻¹ •
          (mixedSeedFieldBlock parameters count (base + t • directions (Fin.last count))
            (fun position => directions position.castSucc) -
           mixedSeedFieldBlock parameters count base (fun position => directions position.castSucc))) -
          mixedSeedFieldBlock parameters (count + 1) base directions))
        (𝓝[≠] (0 : ℝ)) (𝓝 0))
    (order : ℕ) (assignment : Fin order → Fin 2) (base : Input parameters)
    (directions : Fin (order + 1) → Input parameters)
    (inside : base.1 ∈ Grad.Constraints.Seed.parameterDomain)
    (axis : ChartAxisCondition base.2.2) :
    ∀ grade, Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ •
        (mixedRootSeedTerm parameters assignment (base + t • directions (Fin.last order))
          (fun position => directions position.castSucc) -
         mixedRootSeedTerm parameters assignment base (fun position => directions position.castSucc))) -
        (mixedRootSeedTerm parameters (Fin.snoc assignment 0) base directions +
          mixedRootSeedTerm parameters (Fin.snoc assignment 1) base directions)))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  let rootTuple := fiberTuple assignment 0 (fun position => directions position.castSucc)
  let seedTuple := fiberTuple assignment 1 (fun position => directions position.castSucc)
  let newest := directions (Fin.last order)
  have rootRule := mixedRootBlock_genuine parameters (assignmentFiber assignment 0).card base
    (Fin.snoc rootTuple newest) axis
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at rootRule
  have fieldRule := seedRule (assignmentFiber assignment 1).card base (Fin.snoc seedTuple newest) inside
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at fieldRule
  have fieldRule' : ∀ grade, Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ •
        (mixedSeedFieldBlock parameters (assignmentFiber assignment 1).card (base + t • newest) seedTuple -
          mixedSeedFieldBlock parameters (assignmentFiber assignment 1).card (base + (0 : ℝ) • newest) seedTuple)) -
        mixedSeedFieldBlock parameters ((assignmentFiber assignment 1).card + 1) base (Fin.snoc seedTuple newest)))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_smul ℝ newest, add_zero] using fieldRule
  have product := multiplier_curve_genuine parameters
    (fun t : ℝ => mixedRootBlock parameters (assignmentFiber assignment 0).card (base + t • newest) rootTuple)
    (mixedRootBlock parameters ((assignmentFiber assignment 0).card + 1) base (Fin.snoc rootTuple newest))
    (fun t : ℝ => mixedSeedFieldBlock parameters (assignmentFiber assignment 1).card (base + t • newest) seedTuple)
    (mixedSeedFieldBlock parameters ((assignmentFiber assignment 1).card + 1) base (Fin.snoc seedTuple newest))
    rootRule fieldRule'
  have zeroInput : base + (0 : ℝ) • newest = base := by
    rw [zero_smul ℝ newest, add_zero]
  rw [zeroInput] at product
  intro grade
  rw [mixedRootSeedTerm_snoc_zero parameters assignment base directions,
    mixedRootSeedTerm_snoc_one parameters assignment base directions]
  exact product grade

private theorem rootSeedSum_genuine
    (seedRule : ∀ (count : ℕ) (base : Input parameters)
      (directions : Fin (count + 1) → Input parameters),
      base.1 ∈ Grad.Constraints.Seed.parameterDomain → ∀ grade,
      Tendsto (fun t : ℝ => originalGradeNorm grade
        (((t : ℂ)⁻¹ •
          (mixedSeedFieldBlock parameters count (base + t • directions (Fin.last count))
            (fun position => directions position.castSucc) -
           mixedSeedFieldBlock parameters count base (fun position => directions position.castSucc))) -
          mixedSeedFieldBlock parameters (count + 1) base directions))
        (𝓝[≠] (0 : ℝ)) (𝓝 0))
    (order : ℕ) (base : Input parameters) (directions : Fin (order + 1) → Input parameters)
    (inside : base.1 ∈ Grad.Constraints.Seed.parameterDomain)
    (axis : ChartAxisCondition base.2.2) (grade : ℕ) :
    Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ •
        (q23MixedRootSeedField parameters order (base + t • directions (Fin.last order))
          (fun position => directions position.castSucc) -
         q23MixedRootSeedField parameters order base (fun position => directions position.castSucc))) -
        q23MixedRootSeedField parameters (order + 1) base directions))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  let curve (assignment : Fin order → Fin 2) (t : ℝ) :=
    mixedRootSeedTerm parameters assignment (base + t • directions (Fin.last order))
      (fun position => directions position.castSucc)
  let derivative (assignment : Fin order → Fin 2) :=
    mixedRootSeedTerm parameters (Fin.snoc assignment 0) base directions +
      mixedRootSeedTerm parameters (Fin.snoc assignment 1) base directions
  have each (assignment : Fin order → Fin 2) : HasDerivAt
      (fun t : ℝ => fieldEmbed parameters 3 grade (curve assignment t))
      (fieldEmbed parameters 3 grade (derivative assignment)) 0 := by
    apply (coreCurve_hasDerivAt_iff (fieldEmbed parameters 3 grade)
      (originalGradeNorm grade) (fieldEmbed_norm parameters 3 grade) _ _).2
    simpa only [curve, derivative, zero_smul ℝ (directions (Fin.last order)), add_zero] using
      rootSeedTerm_genuine seedRule order assignment base directions inside axis grade
  have total := HasDerivAt.sum (u := Finset.univ) (fun assignment _ => each assignment)
  have functionSum : (∑ assignment : Fin order → Fin 2,
      fun t : ℝ => fieldEmbed parameters 3 grade (curve assignment t)) =
      fun t : ℝ => fieldEmbed parameters 3 grade
        (q23MixedRootSeedField parameters order (base + t • directions (Fin.last order))
          (fun position => directions position.castSucc)) := by
    funext t
    rw [Finset.sum_apply, ← map_sum]
    rfl
  rw [functionSum] at total
  have total' : HasDerivAt
      (fun t : ℝ => fieldEmbed parameters 3 grade
        (q23MixedRootSeedField parameters order (base + t • directions (Fin.last order))
          (fun position => directions position.castSucc)))
      (fieldEmbed parameters 3 grade (q23MixedRootSeedField parameters (order + 1) base directions)) 0 := by
    rw [mixedRootSeedField_succ, map_sum]
    exact total
  have limit := (coreCurve_hasDerivAt_iff (fieldEmbed parameters 3 grade)
    (originalGradeNorm grade) (fieldEmbed_norm parameters 3 grade) _ _).1 total'
  simpa only [zero_smul ℝ (directions (Fin.last order)), add_zero] using limit

/-- The proved seed-field derivative tower in the mixed input's newest-last
ordering. The only conversion is an exact finite tuple identity. -/
theorem mixedSeedFieldBlock_genuine (parameters : PhaseParameters) (order : ℕ)
    (base : Input parameters) (directions : Fin (order + 1) → Input parameters)
    (inside : base.1 ∈ Grad.Constraints.Seed.parameterDomain) (grade : ℕ) :
    Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ •
        (mixedSeedFieldBlock parameters order (base + t • directions (Fin.last order))
          (fun position => directions position.castSucc) -
         mixedSeedFieldBlock parameters order base (fun position => directions position.castSucc))) -
        mixedSeedFieldBlock parameters (order + 1) base directions))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have tuple : Fin.cons (directions (Fin.last order)).1
      (fun position : Fin order => (directions position.rev.castSucc).1) =
      fun position : Fin (order + 1) => (directions position.rev).1 := by
    funext position
    refine Fin.cases ?_ (fun index => ?_) position
    · simp only [Fin.cons_zero, Fin.rev_zero]
    · simp only [Fin.cons_succ, Fin.rev_succ]
  have actual := q23SeedFieldCoreDerivative_genuine parameters order grade base.1 inside
    (fun position => (directions position.rev.castSucc).1) (directions (Fin.last order)).1
  rw [tuple] at actual
  exact actual

/-- The literal root-times-moving-seed allocation sum differentiates to its
next order in every original field norm. This is independent of any later
physical-coordinate correspondence for the reference transfer. -/
theorem q23MixedRootSeedField_genuine (parameters : PhaseParameters) (order : ℕ)
    (base : Input parameters) (directions : Fin (order + 1) → Input parameters)
    (inside : base.1 ∈ Grad.Constraints.Seed.parameterDomain)
    (axis : ChartAxisCondition base.2.2) (grade : ℕ) :
    Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ •
        (q23MixedRootSeedField parameters order (base + t • directions (Fin.last order))
          (fun position => directions position.castSucc) -
         q23MixedRootSeedField parameters order base (fun position => directions position.castSucc))) -
        q23MixedRootSeedField parameters (order + 1) base directions))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
  rootSeedSum_genuine (mixedSeedFieldBlock_genuine parameters) order base directions inside axis grade

end Grad.MixedQuotientComposition
