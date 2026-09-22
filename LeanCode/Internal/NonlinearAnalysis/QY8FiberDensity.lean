import QY7MixedGrades

noncomputable section

open scoped ContDiff

namespace Grad.Q24Realization

/-- Extend an actual mixed derivative bound while holding finite base
parameters fixed. Only the infinite-dimensional state is approximated;
the independent derivative directions are approximated in the full mixed
space. Thus an arbitrary compact seed patch need not have interior. -/
theorem derivative_bound_on_dense_fiber {C D B E F : Type*}
    [TopologicalSpace B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (stateEmbedding : C → B) (stateDense : DenseRange stateEmbedding)
    (directionEmbedding : D → E) (directionDense : DenseRange directionEmbedding)
    (baseMap : B → E) (baseContinuous : Continuous baseMap)
    (mapping : E → F) (domain : Set E) (openDomain : IsOpen domain)
    (smooth : ContDiffOn ℝ ∞ mapping domain) (order : ℕ)
    (low : B → ℝ) (lowContinuous : Continuous low) (threshold : ℝ)
    (majorant : B × (Fin order → E) → ℝ) (majorantContinuous : Continuous majorant)
    (coreBound : ∀ (base : C) (directions : Fin order → D),
      baseMap (stateEmbedding base) ∈ domain → low (stateEmbedding base) < threshold →
      ‖iteratedFDeriv ℝ order mapping (baseMap (stateEmbedding base))
        (fun position => directionEmbedding (directions position))‖ ≤
      majorant (stateEmbedding base, fun position => directionEmbedding (directions position)))
    (base : B) (directions : Fin order → E) (inside : baseMap base ∈ domain)
    (lowBound : low base < threshold) :
    ‖iteratedFDeriv ℝ order mapping (baseMap base) directions‖ ≤ majorant (base, directions) := by
  let tuples : C × (Fin order → D) → B × (Fin order → E) :=
    Prod.map stateEmbedding (fun tuple => fun position => directionEmbedding (tuple position))
  have tuplesDense : DenseRange tuples :=
    stateDense.prodMap (finiteTuples_denseRange directionEmbedding directionDense order)
  let restricted : Set (B × (Fin order → E)) :=
    {pair | baseMap pair.1 ∈ domain ∧ low pair.1 < threshold}
  have restrictedOpen : IsOpen restricted :=
    (openDomain.preimage (baseContinuous.comp continuous_fst)).inter
      (isOpen_lt (lowContinuous.comp continuous_fst) continuous_const)
  have valueContinuous : ContinuousOn
      (fun pair : B × (Fin order → E) =>
        ‖iteratedFDeriv ℝ order mapping (baseMap pair.1) pair.2‖) restricted := by
    have operators : ContinuousOn
        (fun pair : B × (Fin order → E) => iteratedFDeriv ℝ order mapping (baseMap pair.1)) restricted :=
      (continuousOn_actual_iteratedFDeriv openDomain smooth order).comp
        (baseContinuous.comp continuous_fst).continuousOn (fun _ membership => membership.1)
    exact (operators.eval continuous_snd.continuousOn).norm
  exact le_on_open_of_dense tuples tuplesDense restricted restrictedOpen _ majorant
    valueContinuous majorantContinuous.continuousOn
    (fun pair member => coreBound pair.1 pair.2 member.1 member.2)
    (base, directions) ⟨inside, lowBound⟩

end Grad.Q24Realization
