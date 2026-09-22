import Q23TransferProductGenuine

noncomputable section

set_option maxRecDepth 5000
set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

open Set Filter
open scoped Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.Constraints
open Grad.Constraints.Seed

/-- Original-grade genuine core derivatives are closed under addition. -/
theorem q23OriginalGrade_add_genuine
    {phase : PhaseParameters} {dimension grade : ℕ}
    (first second : ℝ → ACore phase dimension)
    (firstDerivative secondDerivative : ACore phase dimension)
    (firstGenuine : Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ • (first t - first 0)) - firstDerivative))
      (𝓝[≠] (0 : ℝ)) (𝓝 0))
    (secondGenuine : Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ • (second t - second 0)) - secondDerivative))
      (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ • ((first t + second t) - (first 0 + second 0))) -
        (firstDerivative + secondDerivative)))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  let embedding := q23ACoreEta phase dimension grade
  have firstRule := (q23CoreCurve_hasDerivAt_iff embedding
    (originalGradeNorm grade)
    (fun value => aGradeEta_norm phase (GradeCore.ofCoreLinear value))
    first firstDerivative).2 firstGenuine
  have secondRule := (q23CoreCurve_hasDerivAt_iff embedding
    (originalGradeNorm grade)
    (fun value => aGradeEta_norm phase (GradeCore.ofCoreLinear value))
    second secondDerivative).2 secondGenuine
  have sumRule := firstRule.add secondRule
  have curveEquality :
      (fun t => embedding (first t + second t)) =
        (fun t => embedding (first t)) + (fun t => embedding (second t)) := by
    funext t
    exact map_add embedding (first t) (second t)
  exact (q23CoreCurve_hasDerivAt_iff embedding (originalGradeNorm grade)
    (fun value => aGradeEta_norm phase (GradeCore.ofCoreLinear value))
    (fun t => first t + second t) (firstDerivative + secondDerivative)).1 (by
      rw [curveEquality, map_add]
      exact sumRule)

private theorem q23TangentAffine_zero_curve
    (phase : PhaseParameters) (base direction : Q23MixedInput phase) (t : ℝ) :
    q23MixedTangentAffine phase 0 (base + t • direction)
        (fun position => position.elim0) =
      q23MixedTangentAffine phase 0 base (fun position => position.elim0) +
        (t : ℂ) • q23MixedTangentAffine phase 1 base (fun _ => direction) := by
  change chartTangentPart phase (base.2.2.1 + t • direction.2.2.1) =
    chartTangentPart phase base.2.2.1 + (t : ℂ) • chartTangentPart phase direction.2.2.1
  rw [show t • direction.2.2.1 = (t : ℂ) • direction.2.2.1 by
    exact Complex.coe_smul t direction.2.2.1]
  rw [chartTangentPart_add, chartTangentPart_smul]

/-- The affine tangential chart term has its literal zero/one/higher
newest-last derivative tower. -/
theorem q23MixedTangentAffine_genuine
    (phase : PhaseParameters) (order grade : ℕ)
    (base : Q23MixedInput phase)
    (directions : Fin (order + 1) → Q23MixedInput phase) :
    Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ •
        (q23MixedTangentAffine phase order
            (base + t • directions (Fin.last order))
            (fun position => directions position.castSucc) -
          q23MixedTangentAffine phase order base
            (fun position => directions position.castSucc))) -
        q23MixedTangentAffine phase (order + 1) base directions))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have zeroLimit : Tendsto (fun _ : ℝ => (0 : ℝ))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := tendsto_const_nhds
  refine zeroLimit.congr' ?_
  apply eventually_nhdsWithin_of_forall
  intro t nonzero
  symm
  change originalGradeNorm grade _ = 0
  have complexNonzero : (t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by simpa using nonzero)
  cases order with
  | zero =>
      change originalGradeNorm grade
        (((t : ℂ)⁻¹ •
          (chartTangentPart phase
              (base.2.2.1 + t • (directions 0).2.2.1) -
            chartTangentPart phase base.2.2.1)) -
          chartTangentPart phase (directions 0).2.2.1) = 0
      rw [show t • (directions 0).2.2.1 =
          (t : ℂ) • (directions 0).2.2.1 by
        exact Complex.coe_smul t (directions 0).2.2.1,
        chartTangentPart_add, chartTangentPart_smul,
        show (chartTangentPart phase base.2.2.1 +
            (t : ℂ) • chartTangentPart phase (directions 0).2.2.1) -
            chartTangentPart phase base.2.2.1 =
          (t : ℂ) • chartTangentPart phase (directions 0).2.2.1 by abel,
        smul_smul, inv_mul_cancel₀ complexNonzero, one_smul, sub_self,
        originalGradeNorm_zero]
  | succ count =>
      cases count with
      | zero =>
          simp [q23MixedTangentAffine, originalGradeNorm_zero]
      | succ count =>
          simp [q23MixedTangentAffine, originalGradeNorm_zero]

/-- The affine potential coordinate has its literal zero/one/higher
newest-last derivative tower. -/
theorem q23MixedPotentialAffine_genuine
    (phase : PhaseParameters) (order grade : ℕ)
    (base : Q23MixedInput phase)
    (directions : Fin (order + 1) → Q23MixedInput phase) :
    Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ •
        (q23MixedPotentialAffine phase order
            (base + t • directions (Fin.last order))
            (fun position => directions position.castSucc) -
          q23MixedPotentialAffine phase order base
            (fun position => directions position.castSucc))) -
        q23MixedPotentialAffine phase (order + 1) base directions))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have zeroLimit : Tendsto (fun _ : ℝ => (0 : ℝ))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := tendsto_const_nhds
  refine zeroLimit.congr' ?_
  apply eventually_nhdsWithin_of_forall
  intro t nonzero
  symm
  change originalGradeNorm grade _ = 0
  have complexNonzero : (t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by simpa using nonzero)
  cases order with
  | zero =>
      change originalGradeNorm grade
        (((t : ℂ)⁻¹ •
          ((base.2.2.2.2 + (t : ℂ) • (directions 0).2.2.2.2) -
            base.2.2.2.2)) - (directions 0).2.2.2.2) = 0
      rw [show (base.2.2.2.2 + (t : ℂ) • (directions 0).2.2.2.2) -
          base.2.2.2.2 = (t : ℂ) • (directions 0).2.2.2.2 by abel,
        smul_smul, inv_mul_cancel₀ complexNonzero, one_smul, sub_self,
        originalGradeNorm_zero]
  | succ count =>
      cases count with
      | zero =>
          simp [q23MixedPotentialAffine, originalGradeNorm_zero]
      | succ count =>
          simp [q23MixedPotentialAffine, originalGradeNorm_zero]

/-- The affine curvature coordinate has its literal zero/one/higher tower. -/
theorem q23ReferenceScalar_genuine
    {phase : PhaseParameters} (order : ℕ)
    (base : Q23MixedInput phase)
    (directions : Fin (order + 1) → Q23MixedInput phase) :
    Tendsto (fun t : ℝ => ‖((t : ℂ)⁻¹ *
      (referenceScalar order (base + t • directions (Fin.last order)).2
          (fun position => (directions position.castSucc).2) -
        referenceScalar order base.2
          (fun position => (directions position.castSucc).2)) -
      referenceScalar (order + 1) base.2 (fun position => (directions position).2))‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have zeroLimit : Tendsto (fun _ : ℝ => (0 : ℝ))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := tendsto_const_nhds
  refine zeroLimit.congr' ?_
  apply eventually_nhdsWithin_of_forall
  intro t nonzero
  symm
  change ‖_‖ = 0
  have complexNonzero : (t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by simpa using nonzero)
  cases order with
  | zero =>
      change ‖(t : ℂ)⁻¹ * ((base.2.1 + (t : ℂ) * (directions 0).2.1) -
        base.2.1) - (directions 0).2.1‖ = 0
      rw [show (base.2.1 + (t : ℂ) * (directions 0).2.1) - base.2.1 =
          (t : ℂ) * (directions 0).2.1 by ring,
        ← mul_assoc, inv_mul_cancel₀ complexNonzero, one_mul, sub_self, norm_zero]
  | succ count =>
      cases count with
      | zero =>
          simp [referenceScalar]
      | succ count =>
          simp [referenceScalar]

/-- The newest-last wrapper of the actual seed-scalar derivative tower. -/
theorem q23SeedScalarDirectionalCoreDerivative_genuine
    (phase : PhaseParameters) (order grade : ℕ)
    (base : Q23MixedInput phase)
    (directions : Fin (order + 1) → Q23MixedInput phase)
    (inside : base.1 ∈ Seed.parameterDomain) :
    Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ •
        (q23SeedScalarDirectionalCoreDerivative phase order
            (base + t • directions (Fin.last order)).1
            (fun position => (directions position.castSucc).1) -
          q23SeedScalarDirectionalCoreDerivative phase order base.1
            (fun position => (directions position.castSucc).1))) -
        q23SeedScalarDirectionalCoreDerivative phase (order + 1) base.1
          (fun position => (directions position).1)))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have tuple : Fin.cons (directions (Fin.last order)).1
      (fun position : Fin order => (directions position.rev.castSucc).1) =
      fun position : Fin (order + 1) => (directions position.rev).1 := by
    funext position
    refine Fin.cases ?_ (fun index => ?_) position
    · simp only [Fin.cons_zero, Fin.rev_zero]
    · simp only [Fin.cons_succ, Fin.rev_succ]
  have actual := q23SeedScalarCoreDerivative_genuine phase order grade base.1 inside
    (fun position => (directions position.rev.castSucc).1)
    (directions (Fin.last order)).1
  rw [tuple] at actual
  exact actual

end Grad.NonlinearQuotientBounds
