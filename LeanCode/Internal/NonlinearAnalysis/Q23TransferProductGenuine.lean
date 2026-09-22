import Q23SeedFamilyGenuine

noncomputable section

set_option maxRecDepth 5000
set_option maxHeartbeats 8000000

open Set Filter
open scoped BigOperators ContDiff Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.Constraints
open Grad.Constraints.Gauges Grad.Constraints.Seed

variable {phase : PhaseParameters}

/-- A core curve has the stated original-grade directional limit exactly
when its isometric completed image has the corresponding real derivative. -/
theorem q23CoreCurve_hasDerivAt_iff {Core E : Type*}
    [AddCommGroup Core] [Module ℂ Core]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E]
    (embedding : Core →ₗ[ℂ] E) (coreNorm : Core → ℝ)
    (normIdentity : ∀ value, ‖embedding value‖ = coreNorm value)
    (curve : ℝ → Core) (derivative : Core) :
    HasDerivAt (fun t : ℝ => embedding (curve t)) (embedding derivative) 0 ↔
      Tendsto (fun t : ℝ => coreNorm
        (((t : ℂ)⁻¹ • (curve t - curve 0)) - derivative))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  have identity :
      (fun t : ℝ => ‖slope (fun r : ℝ => embedding (curve r)) 0 t -
        embedding derivative‖) =
      fun t : ℝ => coreNorm
        (((t : ℂ)⁻¹ • (curve t - curve 0)) - derivative) := by
    funext t
    rw [slope_def_module, sub_zero, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    change ‖((t⁻¹ : ℝ) : ℂ) • (embedding (curve t) - embedding (curve 0)) -
      embedding derivative‖ = _
    rw [Complex.ofReal_inv, ← map_sub, ← map_smul, ← map_sub, normIdentity]
  rw [identity]

private theorem q23MixedVectorAffine_hasDerivAt
    (phase : PhaseParameters) (grade order : ℕ)
    (base : Q23MixedInput phase)
    (directions : Fin (order + 1) → Q23MixedInput phase) :
    HasDerivAt
      (fun t : ℝ => q23ACoreEta phase 3 grade
        (q23MixedVectorAffine phase order
          (base + t • directions (Fin.last order))
          (fun position => directions position.castSucc)))
      (q23ACoreEta phase 3 grade
        (q23MixedVectorAffine phase (order + 1) base directions)) 0 := by
  cases order with
  | zero =>
      change HasDerivAt
        (fun t : ℝ => q23ACoreEta phase 3 grade
          (base.2.2.2.1 + t • (directions 0).2.2.2.1))
        (q23ACoreEta phase 3 grade (directions 0).2.2.2.1) 0
      have line := ((hasDerivAt_id (0 : ℝ)).smul_const
        (q23ACoreEta phase 3 grade (directions 0).2.2.2.1)).const_add
          (q23ACoreEta phase 3 grade base.2.2.2.1)
      have curveEquality :
          (fun t : ℝ => q23ACoreEta phase 3 grade
            (base.2.2.2.1 + t • (directions 0).2.2.2.1)) =
          (fun t : ℝ => q23ACoreEta phase 3 grade base.2.2.2.1 +
            t • q23ACoreEta phase 3 grade (directions 0).2.2.2.1) := by
        funext t
        rw [map_add]
        exact congrArg (fun value =>
          q23ACoreEta phase 3 grade base.2.2.2.1 + value)
          (((q23ACoreEta phase 3 grade).restrictScalars ℝ).map_smul
            t (directions 0).2.2.2.1)
      rw [curveEquality]
      simpa only [Function.comp_apply, id_eq, one_smul] using line
  | succ count =>
      cases count with
      | zero =>
          change HasDerivAt
            (fun _ : ℝ => q23ACoreEta phase 3 grade
              (directions (Fin.castSucc 0)).2.2.2.1)
            (q23ACoreEta phase 3 grade (0 : ACore phase 3)) 0
          rw [map_zero]
          exact hasDerivAt_const (0 : ℝ) _
      | succ count =>
          change HasDerivAt
            (fun _ : ℝ => q23ACoreEta phase 3 grade (0 : ACore phase 3))
            (q23ACoreEta phase 3 grade (0 : ACore phase 3)) 0
          rw [map_zero]
          exact hasDerivAt_const (0 : ℝ) _

/-- One allocation term in the derivative of the moving N18 operator applied
to the affine vector slot. -/
def q23MixedTransferTerm (phase : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    {order : ℕ} (assignment : Fin order → Fin 2)
    (base : Q23MixedInput phase) (directions : Fin order → Q23MixedInput phase) :
    ACore phase 3 :=
  q23SeedTransferDirectionalCoreDerivative phase reference insideR
    (assignmentFiber assignment 0).card base.1
    (fun position => (q23FiberTuple assignment 0 directions position).1)
    (q23MixedVectorAffine phase (assignmentFiber assignment 1).card base
      (q23FiberTuple assignment 1 directions))

private theorem q23MixedFamily_cast {Value : Type*}
    (family : (order : ℕ) → Q23MixedInput phase →
      (Fin order → Q23MixedInput phase) → Value)
    {count count' : ℕ} (equal : count = count') (base : Q23MixedInput phase)
    (tuple : Fin count' → Q23MixedInput phase) :
    family count base (tuple ∘ Fin.cast equal) = family count' base tuple := by
  subst equal
  rfl

private theorem q23FiberTuple_snoc_of_ne {order slots : ℕ}
    (assignment : Fin order → Fin slots) (slot other : Fin slots)
    (ne : other ≠ slot) (directions : Fin (order + 1) → Q23MixedInput phase) :
    q23FiberTuple (Fin.snoc assignment slot) other directions =
      q23FiberTuple assignment other
          (fun position => directions position.castSucc) ∘
        Fin.cast (card_assignmentFiber_snoc_of_ne assignment slot ne) := by
  funext index
  unfold q23FiberTuple
  rw [fiberEnumeration_snoc_of_ne assignment slot ne]
  rfl

private theorem q23FiberTuple_snoc_self {order slots : ℕ}
    (assignment : Fin order → Fin slots) (slot : Fin slots)
    (directions : Fin (order + 1) → Q23MixedInput phase) :
    q23FiberTuple (Fin.snoc assignment slot) slot directions =
      Fin.snoc (q23FiberTuple assignment slot
          (fun position => directions position.castSucc))
        (directions (Fin.last order)) ∘
        Fin.cast (card_assignmentFiber_snoc_self assignment slot) := by
  funext index
  unfold q23FiberTuple
  rw [fiberEnumeration_snoc_self assignment slot]
  show directions (Fin.snoc (α := fun _ => Fin (order + 1))
      (Fin.castSucc ∘ fiberEnumeration assignment slot) (Fin.last order)
      (Fin.cast (card_assignmentFiber_snoc_self assignment slot) index)) =
    Fin.snoc (α := fun _ : Fin ((assignmentFiber assignment slot).card + 1) =>
        Q23MixedInput phase) (q23FiberTuple assignment slot
      (fun position => directions position.castSucc))
      (directions (Fin.last order))
      (Fin.cast (card_assignmentFiber_snoc_self assignment slot) index)
  rcases Fin.eq_castSucc_or_eq_last
    (Fin.cast (card_assignmentFiber_snoc_self assignment slot) index) with
    ⟨q, equality⟩ | equality
  · rw [equality, Fin.snoc_castSucc, Fin.snoc_castSucc]
    rfl
  · rw [equality, Fin.snoc_last, Fin.snoc_last]

private theorem q23MixedTransferTerm_snoc_zero
    (phase : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) {order : ℕ}
    (assignment : Fin order → Fin 2) (base : Q23MixedInput phase)
    (directions : Fin (order + 1) → Q23MixedInput phase) :
    q23MixedTransferTerm phase reference insideR (Fin.snoc assignment 0) base directions =
      q23SeedTransferDirectionalCoreDerivative phase reference insideR
        ((assignmentFiber assignment 0).card + 1) base.1
        (fun position =>
          (Fin.snoc (α := fun _ : Fin ((assignmentFiber assignment 0).card + 1) =>
              Q23MixedInput phase) (q23FiberTuple assignment 0
              (fun index : Fin order => directions index.castSucc))
            (directions (Fin.last order)) position).1)
        (q23MixedVectorAffine phase (assignmentFiber assignment 1).card base
          (q23FiberTuple assignment 1
            (fun index : Fin order => directions index.castSucc))) := by
  unfold q23MixedTransferTerm
  rw [q23FiberTuple_snoc_self,
    q23FiberTuple_snoc_of_ne assignment 0 1 (by decide),
    q23MixedFamily_cast (fun count point tuple =>
      q23SeedTransferDirectionalCoreDerivative phase reference insideR count point.1
        (fun position => (tuple position).1)),
    q23MixedFamily_cast (q23MixedVectorAffine phase)]

private theorem q23MixedTransferTerm_snoc_one
    (phase : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) {order : ℕ}
    (assignment : Fin order → Fin 2) (base : Q23MixedInput phase)
    (directions : Fin (order + 1) → Q23MixedInput phase) :
    q23MixedTransferTerm phase reference insideR (Fin.snoc assignment 1) base directions =
      q23SeedTransferDirectionalCoreDerivative phase reference insideR
        (assignmentFiber assignment 0).card base.1
        (fun position =>
          (q23FiberTuple assignment 0
            (fun index : Fin order => directions index.castSucc) position).1)
        (q23MixedVectorAffine phase ((assignmentFiber assignment 1).card + 1) base
          (Fin.snoc (α := fun _ : Fin ((assignmentFiber assignment 1).card + 1) =>
              Q23MixedInput phase) (q23FiberTuple assignment 1
              (fun index : Fin order => directions index.castSucc))
            (directions (Fin.last order)))) := by
  unfold q23MixedTransferTerm
  rw [q23FiberTuple_snoc_of_ne assignment 1 0 (by decide),
    q23FiberTuple_snoc_self,
    q23MixedFamily_cast (fun count point tuple =>
      q23SeedTransferDirectionalCoreDerivative phase reference insideR count point.1
        (fun position => (tuple position).1)),
    q23MixedFamily_cast (q23MixedVectorAffine phase)]

private theorem q23ReverseSnoc_seedTuple {order : ℕ}
    (directions : Fin order → Q23MixedInput phase)
    (newest : Q23MixedInput phase) :
    Fin.cons newest.1 (fun position => (directions position.rev).1) =
      fun position => (Fin.snoc
        (α := fun _ : Fin (order + 1) => Q23MixedInput phase)
        directions newest position.rev).1 := by
  funext position
  rcases Fin.eq_zero_or_eq_succ position with rfl | ⟨position, rfl⟩
  · rw [Fin.cons_zero, Fin.rev_zero, Fin.snoc_last]
  · rw [Fin.cons_succ, Fin.rev_succ, Fin.snoc_castSucc]

private theorem q23RealSeedTransferDerivative_eq
    (phase : PhaseParameters) (grade order : ℕ)
    (reference parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    iteratedFDeriv ℝ order
        (fun point => q23RestrictScalarsCLM
          (completedSeedTransferFamily phase grade reference point))
        parameter directions =
      q23RestrictScalarsCLM
        (completedSeedTransferParameterDerivative phase grade order
          reference parameter directions) := by
  let restriction := q23RestrictScalarsCLM
    (E := AGrade phase 3 grade) (F := AGrade phase 3 grade)
  have smoothAt :=
    (completedSeedTransferFamily_contDiffOn phase grade reference).contDiffAt
      (Seed.parameterDomain_isOpen.mem_nhds inside)
  have mapped := q23IteratedFDeriv_linearFunction_comp
    (fun operator => restriction operator) restriction.map_add restriction.map_smul
    restriction.continuous (completedSeedTransferFamily phase grade reference)
    parameter smoothAt order directions
  simpa only [restriction, completedSeedTransferParameterDerivative] using mapped

private theorem q23MixedTransferTerm_hasDerivAt
    (phase : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (order : ℕ)
    (assignment : Fin order → Fin 2) (base : Q23MixedInput phase)
    (directions : Fin (order + 1) → Q23MixedInput phase)
    (inside : base.1 ∈ Seed.parameterDomain) (grade : ℕ) :
    HasDerivAt
      (fun t : ℝ => q23ACoreEta phase 3 grade
        (q23MixedTransferTerm phase reference insideR assignment
          (base + t • directions (Fin.last order))
          (fun position => directions position.castSucc)))
      (q23ACoreEta phase 3 grade
        (q23MixedTransferTerm phase reference insideR (Fin.snoc assignment 0)
            base directions +
          q23MixedTransferTerm phase reference insideR (Fin.snoc assignment 1)
            base directions)) 0 := by
  let oldDirections : Fin order → Q23MixedInput phase :=
    fun position => directions position.castSucc
  let seedTuple := q23FiberTuple assignment 0 oldDirections
  let vectorTuple := q23FiberTuple assignment 1 oldDirections
  let newest := directions (Fin.last order)
  let actualSeedDirections : Fin (assignmentFiber assignment 0).card → Seed.Parameters :=
    fun position => (seedTuple position.rev).1
  let realFamily := fun point => q23RestrictScalarsCLM
    (completedSeedTransferFamily phase grade reference point)
  let operatorCurve := fun t : ℝ =>
    iteratedFDeriv ℝ (assignmentFiber assignment 0).card realFamily
      (base.1 + t • newest.1) actualSeedDirections
  let operatorDerivative :=
    iteratedFDeriv ℝ ((assignmentFiber assignment 0).card + 1) realFamily base.1
      (Fin.cons newest.1 actualSeedDirections)
  have realSmooth : ContDiffOn ℝ ∞ realFamily Seed.parameterDomain :=
    (q23RestrictScalarsCLM
      (E := AGrade phase 3 grade) (F := AGrade phase 3 grade)).contDiff.comp_contDiffOn
        (completedSeedTransferFamily_contDiffOn phase grade reference)
  have operatorRule : HasDerivAt operatorCurve operatorDerivative 0 := by
    have raw := (q23IteratedFDeriv_line_hasFDerivAt
        realFamily
        Seed.parameterDomain Seed.parameterDomain_isOpen
        realSmooth
        (assignmentFiber assignment 0).card base.1 inside
        actualSeedDirections newest.1).hasDerivAt
    simpa only [operatorCurve, operatorDerivative,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      one_smul] using raw
  have vectorRule := q23MixedVectorAffine_hasDerivAt phase grade
    (assignmentFiber assignment 1).card base (Fin.snoc vectorTuple newest)
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at vectorRule
  have productRule := operatorRule.clm_apply vectorRule
  have near : ∀ᶠ t : ℝ in 𝓝 0, base.1 + t • newest.1 ∈ Seed.parameterDomain := by
    have lineContinuous : ContinuousAt (fun t : ℝ => base.1 + t • newest.1) 0 := by
      fun_prop
    exact lineContinuous.preimage_mem_nhds
      (Seed.parameterDomain_isOpen.mem_nhds (by simpa using inside))
  have productAgreement :
      (fun t : ℝ => operatorCurve t
        (q23ACoreEta phase 3 grade
          (q23MixedVectorAffine phase (assignmentFiber assignment 1).card
            (base + t • newest) vectorTuple))) =ᶠ[𝓝 0]
      (fun t : ℝ => q23ACoreEta phase 3 grade
        (q23MixedTransferTerm phase reference insideR assignment
          (base + t • newest) oldDirections)) := by
    filter_upwards [near] with t movedInside
    simp only [operatorCurve]
    rw [q23RealSeedTransferDerivative_eq phase grade
      (assignmentFiber assignment 0).card reference
      (base.1 + t • newest.1) movedInside actualSeedDirections]
    change completedSeedTransferParameterDerivative phase grade
        (assignmentFiber assignment 0).card reference
        (base.1 + t • newest.1) actualSeedDirections
        (q23ACoreEta phase 3 grade
          (q23MixedVectorAffine phase (assignmentFiber assignment 1).card
            (base + t • newest) vectorTuple)) = _
    rw [completedSeedTransferFamily_all_orders_core phase grade reference insideR
      (assignmentFiber assignment 0).card (base.1 + t • newest.1) movedInside
      actualSeedDirections]
    rfl
  have tupleEquality :
      Fin.cons newest.1 actualSeedDirections =
        fun position =>
          (Fin.snoc
            (α := fun _ : Fin ((assignmentFiber assignment 0).card + 1) =>
              Q23MixedInput phase)
            seedTuple newest position.rev).1 := by
    exact q23ReverseSnoc_seedTuple seedTuple newest
  have firstCore := completedSeedTransferFamily_all_orders_core phase grade
    reference insideR ((assignmentFiber assignment 0).card + 1) base.1 inside
    (Fin.cons newest.1 actualSeedDirections)
    (q23MixedVectorAffine phase (assignmentFiber assignment 1).card base vectorTuple)
  have firstCoreReversed := firstCore
  rw [tupleEquality] at firstCoreReversed
  have secondCore := completedSeedTransferFamily_all_orders_core phase grade
    reference insideR (assignmentFiber assignment 0).card base.1 inside
    actualSeedDirections
    (q23MixedVectorAffine phase ((assignmentFiber assignment 1).card + 1) base
      (Fin.snoc vectorTuple newest))
  have zeroInput : base + (0 : ℝ) • newest = base := by
    calc
      base + (0 : ℝ) • newest = base + 0 :=
        congrArg (fun value => base + value) (zero_smul ℝ newest)
      _ = base := add_zero base
  rw [zeroInput] at productRule
  have derivativeEquality :
      operatorDerivative
          (q23ACoreEta phase 3 grade
            (q23MixedVectorAffine phase (assignmentFiber assignment 1).card base vectorTuple)) +
        operatorCurve 0
          (q23ACoreEta phase 3 grade
            (q23MixedVectorAffine phase ((assignmentFiber assignment 1).card + 1)
              base (Fin.snoc vectorTuple newest))) =
      q23ACoreEta phase 3 grade
        (q23MixedTransferTerm phase reference insideR (Fin.snoc assignment 0)
            base directions +
          q23MixedTransferTerm phase reference insideR (Fin.snoc assignment 1)
            base directions) := by
    rw [q23MixedTransferTerm_snoc_zero, q23MixedTransferTerm_snoc_one,
      map_add]
    simp only [operatorDerivative]
    rw [q23RealSeedTransferDerivative_eq phase grade
      ((assignmentFiber assignment 0).card + 1) reference base.1 inside
      (Fin.cons newest.1 actualSeedDirections)]
    simp only [operatorCurve, zero_smul ℝ newest.1, add_zero]
    rw [q23RealSeedTransferDerivative_eq phase grade
      (assignmentFiber assignment 0).card reference base.1 inside
      actualSeedDirections]
    have restrictionApply (operator : AGrade phase 3 grade →L[ℂ] AGrade phase 3 grade)
        (value : AGrade phase 3 grade) :
        q23RestrictScalarsCLM operator value = operator value := rfl
    rw [restrictionApply, restrictionApply, tupleEquality, firstCoreReversed, secondCore]
    rfl
  have embeddedRule : HasDerivAt
      (fun t : ℝ => q23ACoreEta phase 3 grade
        (q23MixedTransferTerm phase reference insideR assignment
          (base + t • newest) oldDirections))
      (q23ACoreEta phase 3 grade
        (q23MixedTransferTerm phase reference insideR (Fin.snoc assignment 0)
            base directions +
          q23MixedTransferTerm phase reference insideR (Fin.snoc assignment 1)
            base directions)) 0 :=
    (productRule.congr_deriv derivativeEquality).congr_of_eventuallyEq
      productAgreement.symm
  simpa only [oldDirections, newest] using embeddedRule

private theorem q23MixedTransferTerm_genuine
    (phase : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (order : ℕ)
    (assignment : Fin order → Fin 2) (base : Q23MixedInput phase)
    (directions : Fin (order + 1) → Q23MixedInput phase)
    (inside : base.1 ∈ Seed.parameterDomain) (grade : ℕ) :
    Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ •
        (q23MixedTransferTerm phase reference insideR assignment
            (base + t • directions (Fin.last order))
            (fun position => directions position.castSucc) -
          q23MixedTransferTerm phase reference insideR assignment base
            (fun position => directions position.castSucc))) -
        (q23MixedTransferTerm phase reference insideR (Fin.snoc assignment 0)
            base directions +
          q23MixedTransferTerm phase reference insideR (Fin.snoc assignment 1)
            base directions)))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have derivative := q23MixedTransferTerm_hasDerivAt phase reference insideR order
    assignment base directions inside grade
  have limit := (q23CoreCurve_hasDerivAt_iff (q23ACoreEta phase 3 grade)
    (originalGradeNorm grade)
    (fun value => aGradeEta_norm phase (GradeCore.ofCoreLinear value)) _ _).1 derivative
  simpa only [zero_smul ℝ (directions (Fin.last order)), add_zero] using limit

theorem q23MixedTransferredVector_succ
    (phase : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (order : ℕ)
    (base : Q23MixedInput phase)
    (directions : Fin (order + 1) → Q23MixedInput phase) :
    q23MixedTransferredVector phase reference insideR (order + 1) base directions =
      ∑ assignment : Fin order → Fin 2,
        (q23MixedTransferTerm phase reference insideR (Fin.snoc assignment 0)
            base directions +
          q23MixedTransferTerm phase reference insideR (Fin.snoc assignment 1)
            base directions) := by
  change (∑ assignment : Fin (order + 1) → Fin 2,
    q23MixedTransferTerm phase reference insideR assignment base directions) = _
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => Fin 2))
    (fun pair => q23MixedTransferTerm phase reference insideR
      (Fin.snoc pair.2 pair.1) base directions)
    (fun extended => q23MixedTransferTerm phase reference insideR
      extended base directions) (fun _ => rfl),
    Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Fin.sum_univ_two]

/-- The N18 moving-seed transfer applied to the affine vector coordinate is
a genuine newest-last derivative tower in every original grade. -/
theorem q23MixedTransferredVector_genuine
    (phase : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (order : ℕ)
    (base : Q23MixedInput phase)
    (directions : Fin (order + 1) → Q23MixedInput phase)
    (inside : base.1 ∈ Seed.parameterDomain) (grade : ℕ) :
    Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ •
        (q23MixedTransferredVector phase reference insideR order
            (base + t • directions (Fin.last order))
            (fun position => directions position.castSucc) -
          q23MixedTransferredVector phase reference insideR order base
            (fun position => directions position.castSucc))) -
        q23MixedTransferredVector phase reference insideR (order + 1)
          base directions))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  let oldDirections : Fin order → Q23MixedInput phase :=
    fun position => directions position.castSucc
  let newest := directions (Fin.last order)
  let curve (assignment : Fin order → Fin 2) (t : ℝ) :=
    q23MixedTransferTerm phase reference insideR assignment
      (base + t • newest) oldDirections
  let derivative (assignment : Fin order → Fin 2) :=
    q23MixedTransferTerm phase reference insideR (Fin.snoc assignment 0)
        base directions +
      q23MixedTransferTerm phase reference insideR (Fin.snoc assignment 1)
        base directions
  have each (assignment : Fin order → Fin 2) : HasDerivAt
      (fun t : ℝ => q23ACoreEta phase 3 grade (curve assignment t))
      (q23ACoreEta phase 3 grade (derivative assignment)) 0 := by
    simpa only [curve, derivative, oldDirections, newest] using
      q23MixedTransferTerm_hasDerivAt phase reference insideR order assignment
        base directions inside grade
  have total := HasDerivAt.sum (u := Finset.univ) (fun assignment _ => each assignment)
  have curveEquality :
      (fun t : ℝ => q23ACoreEta phase 3 grade
        (q23MixedTransferredVector phase reference insideR order
          (base + t • newest) oldDirections)) =
      ∑ assignment : Fin order → Fin 2,
        fun t : ℝ => q23ACoreEta phase 3 grade (curve assignment t) := by
    funext t
    rw [Finset.sum_apply, ← map_sum]
    rfl
  have total' : HasDerivAt
      (fun t : ℝ => q23ACoreEta phase 3 grade
        (q23MixedTransferredVector phase reference insideR order
          (base + t • newest) oldDirections))
      (q23ACoreEta phase 3 grade
        (q23MixedTransferredVector phase reference insideR (order + 1)
          base directions)) 0 := by
    rw [curveEquality, q23MixedTransferredVector_succ, map_sum]
    simpa only [derivative] using total
  have limit := (q23CoreCurve_hasDerivAt_iff (q23ACoreEta phase 3 grade)
    (originalGradeNorm grade)
    (fun value => aGradeEta_norm phase (GradeCore.ofCoreLinear value)) _ _).1 total'
  simpa only [oldDirections, newest, zero_smul ℝ (directions (Fin.last order)),
    add_zero] using limit

end Grad.NonlinearQuotientBounds
