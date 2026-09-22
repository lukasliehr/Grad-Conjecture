import Q24FixedSeedMap

noncomputable section

open Filter
open scoped Topology ContDiff

namespace Grad.Q24Realization

theorem le_on_open_of_dense {C E : Type*} [TopologicalSpace E]
    (embedding : C → E) (dense : DenseRange embedding) (domain : Set E)
    (openDomain : IsOpen domain) (first second : E → ℝ)
    (firstContinuous : ContinuousOn first domain) (secondContinuous : ContinuousOn second domain)
    (bounded : ∀ core, embedding core ∈ domain → first (embedding core) ≤ second (embedding core))
    (point : E) (inside : point ∈ domain) : first point ≤ second point := by
  by_contra contrary
  have strict : second point < first point := lt_of_not_ge contrary
  have nearby := ((secondContinuous point inside).continuousAt (openDomain.mem_nhds inside)).eventually_lt
    ((firstContinuous point inside).continuousAt (openDomain.mem_nhds inside)) strict
  obtain ⟨core, membership, strictAtCore⟩ := dense.mem_nhds
    (inter_mem (openDomain.mem_nhds inside) nearby)
  exact (not_lt_of_ge (bounded core membership)) strictAtCore

theorem finiteTuples_denseRange {C E : Type*} [TopologicalSpace E]
    (embedding : C → E) (dense : DenseRange embedding) (arity : ℕ) :
    DenseRange (fun arguments : Fin arity → C => fun position => embedding (arguments position)) := by
  classical
  have denseTuples := dense_pi Set.univ (fun _ : Fin arity => fun _ => dense)
  apply denseTuples.mono
  intro tuple member
  choose arguments agreement using fun position => member position (Set.mem_univ position)
  exact ⟨arguments, funext agreement⟩

theorem eq_on_open_of_dense {C E F : Type*} [TopologicalSpace E] [NormedAddCommGroup F]
    (embedding : C → E) (dense : DenseRange embedding) (domain : Set E)
    (openDomain : IsOpen domain) (first second : E → F)
    (firstContinuous : ContinuousOn first domain) (secondContinuous : ContinuousOn second domain)
    (agreement : ∀ core, embedding core ∈ domain → first (embedding core) = second (embedding core))
    (point : E) (inside : point ∈ domain) : first point = second point := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  exact le_on_open_of_dense embedding dense domain openDomain
    (fun value => ‖first value - second value‖) (fun _ => 0)
    (firstContinuous.sub secondContinuous).norm continuousOn_const
    (fun core member => by rw [agreement core member, sub_self, norm_zero]) point inside

theorem continuousOn_actual_iteratedFDeriv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {mapping : E → F} {domain : Set E} (openDomain : IsOpen domain)
    (smooth : ContDiffOn ℝ ∞ mapping domain) (order : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ order mapping) domain := by
  intro point inside
  exact (((smooth point inside).contDiffAt (openDomain.mem_nhds inside)).differentiableAt_iteratedFDeriv
    (m := order) (by exact_mod_cast (WithTop.coe_lt_top order : (order : ℕ∞) < ⊤))).continuousAt.continuousWithinAt

theorem derivative_compatibility_of_dense_core {C E E' F F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (embedding : C → E) (dense : DenseRange embedding)
    (input : E →L[ℝ] E') (output : F →L[ℝ] F')
    (first : E → F) (second : E' → F')
    (domain : Set E) (targetDomain : Set E')
    (openDomain : IsOpen domain) (openTarget : IsOpen targetDomain)
    (maps : Set.MapsTo input domain targetDomain)
    (firstSmooth : ContDiffOn ℝ ∞ first domain)
    (secondSmooth : ContDiffOn ℝ ∞ second targetDomain) (order : ℕ)
    (agreement : ∀ (base : C) (directions : Fin order → C), embedding base ∈ domain →
      output (iteratedFDeriv ℝ order first (embedding base) (fun position => embedding (directions position))) =
      iteratedFDeriv ℝ order second (input (embedding base)) (fun position => input (embedding (directions position))))
    (base : E) (directions : Fin order → E) (inside : base ∈ domain) :
    output (iteratedFDeriv ℝ order first base directions) =
      iteratedFDeriv ℝ order second (input base) (fun position => input (directions position)) := by
  let tuples : C × (Fin order → C) → E × (Fin order → E) :=
    Prod.map embedding (fun tuple => fun position => embedding (tuple position))
  have tuplesDense : DenseRange tuples := dense.prodMap (finiteTuples_denseRange embedding dense order)
  let restricted : Set (E × (Fin order → E)) := {pair | pair.1 ∈ domain}
  have restrictedOpen : IsOpen restricted := openDomain.preimage continuous_fst
  have firstOperators : ContinuousOn
      (fun pair : E × (Fin order → E) => iteratedFDeriv ℝ order first pair.1) restricted :=
    (continuousOn_actual_iteratedFDeriv openDomain firstSmooth order).comp continuous_fst.continuousOn
      (fun _ member => member)
  have secondOperators : ContinuousOn
      (fun pair : E × (Fin order → E) => iteratedFDeriv ℝ order second (input pair.1)) restricted :=
    (continuousOn_actual_iteratedFDeriv openTarget secondSmooth order).comp
      (input.continuous.comp continuous_fst).continuousOn (fun _ member => maps member)
  have loweredDirections : Continuous (fun pair : E × (Fin order → E) =>
      fun position => input (pair.2 position)) := by fun_prop
  exact eq_on_open_of_dense tuples tuplesDense restricted restrictedOpen _ _
    (output.continuous.comp_continuousOn (firstOperators.eval continuous_snd.continuousOn))
    (secondOperators.eval loweredDirections.continuousOn)
    (fun pair member => agreement pair.1 pair.2 member) (base, directions) inside

/-- Extend a continuous derivative estimate through a dense core inside an
open low-domain. All structures are abstract here to avoid concrete carrier
instance diamonds in the subsequent application. -/
theorem derivative_bound_of_dense_core {C E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (embedding : C → E) (dense : DenseRange embedding) (mapping : E → F)
    (domain : Set E) (openDomain : IsOpen domain) (smooth : ContDiffOn ℝ ∞ mapping domain)
    (order : ℕ) (low : E → ℝ) (lowContinuous : Continuous low) (threshold : ℝ)
    (majorant : E × (Fin order → E) → ℝ) (majorantContinuous : Continuous majorant)
    (coreBound : ∀ (base : C) (directions : Fin order → C), embedding base ∈ domain →
      low (embedding base) < threshold →
      ‖iteratedFDeriv ℝ order mapping (embedding base) (fun position => embedding (directions position))‖ ≤
        majorant (embedding base, fun position => embedding (directions position)))
    (base : E) (directions : Fin order → E) (inside : base ∈ domain) (lowBound : low base < threshold) :
    ‖iteratedFDeriv ℝ order mapping base directions‖ ≤ majorant (base, directions) := by
  let tuples : C × (Fin order → C) → E × (Fin order → E) :=
    Prod.map embedding (fun tuple => fun position => embedding (tuple position))
  have tuplesDense : DenseRange tuples := dense.prodMap (finiteTuples_denseRange embedding dense order)
  let restricted : Set (E × (Fin order → E)) := {pair | pair.1 ∈ domain ∧ low pair.1 < threshold}
  have restrictedOpen : IsOpen restricted :=
    (openDomain.preimage continuous_fst).inter (isOpen_lt (lowContinuous.comp continuous_fst) continuous_const)
  have valueContinuous : ContinuousOn
      (fun pair : E × (Fin order → E) => ‖iteratedFDeriv ℝ order mapping pair.1 pair.2‖) restricted := by
    have operators : ContinuousOn
        (fun pair : E × (Fin order → E) => iteratedFDeriv ℝ order mapping pair.1) restricted :=
      (continuousOn_actual_iteratedFDeriv openDomain smooth order).comp continuous_fst.continuousOn
        (fun _ membership => membership.1)
    exact (operators.eval continuous_snd.continuousOn).norm
  exact le_on_open_of_dense tuples tuplesDense restricted restrictedOpen _ majorant
    valueContinuous majorantContinuous.continuousOn
    (fun pair member => coreBound pair.1 pair.2 member.1 member.2)
    (base, directions) ⟨inside, lowBound⟩

end Grad.Q24Realization
