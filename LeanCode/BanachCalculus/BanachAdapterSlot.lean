import BanachAdapterInterface
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.DenseEmbedding
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# NG_F07, step 1: slot completion of bounded multilinear core maps

Steps 1–2 of the supplied proof: a multilinear map on the dense cores, bounded
by `K * ∏ ‖h i‖ * ‖f‖`, extends uniquely to a continuous multilinear map on the
completions (direction slots and source slot), and the completed operator norm
is bounded by every core constant — "take completed operator norms only after
slot completion".

The extension is built one direction slot at a time (left currying): the
curried core map at a core direction extends by induction; the resulting map
of the direction is linear (by uniqueness of continuous extensions, i.e. the
one-difference telescoping estimate in its closed form) and bounded, hence
extends along the dense isometric inclusion of the core by
`ContinuousLinearMap.extend`; uncurrying gives the completed map.  The base
case (no direction slots) is the linear extension in the source slot.
-/

universe u v w

namespace Grad.FiniteBanachCalculus

/-- A bounded linear map on a dense submodule extends to the ambient space.
The abstract target keeps the uniform-space extension API separate from the
nested multilinear target used in slot induction. -/
theorem dense_submodule_clm_extension {X T : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
    {C : Submodule ℝ X} (hC : Dense (C : Set X)) (B : C →L[ℝ] T) :
    ∃ Bx : X →L[ℝ] T, ∀ c : C, Bx c = B c := by
  refine ⟨B.extend C.subtypeL, fun c => ?_⟩
  exact ContinuousLinearMap.extend_eq B hC.denseRange_val
    isUniformEmbedding_subtype_val.isUniformInducing c

section Slot

variable {X : Type u} {F : Type v} {E : Type w}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {C : Submodule ℝ X} {CF : Submodule ℝ F}

/-- Core tuples are dense in the product of the direction-tuple space and the source. -/
theorem dense_coreTuples (hC : Dense (C : Set X)) (hCF : Dense (CF : Set F)) (j : ℕ) :
    Dense ((Set.pi Set.univ fun _ : Fin j => (C : Set X)) ×ˢ (CF : Set F)) :=
  (dense_pi Set.univ fun _ _ => hC).prod hCF

/-- Coercion of a `Fin.cons` core tuple. -/
theorem coe_comp_cons {j : ℕ} (a : C) (h : Fin j → C) :
    (fun i => ((Fin.cons a h : Fin (j + 1) → C) i : X)) =
      Fin.cons (a : X) (fun i => (h i : X)) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp

omit [CompleteSpace E] in
/-- A continuous multilinear map on the completions whose values on core tuples
obey the multilinear bound `K` has completed operator norm at most `K`. -/
theorem opNorm_le_of_core_bound (hC : Dense (C : Set X)) (hCF : Dense (CF : Set F)) {j : ℕ}
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin j => X) (F →L[ℝ] E)) {K : ℝ} (hK : 0 ≤ K)
    (hB : ∀ (h : Fin j → C) (f : CF), ‖B (fun i => (h i : X)) f‖ ≤ K * (∏ i, ‖h i‖) * ‖f‖) :
    ‖B‖ ≤ K := by
  have hall : ∀ p : (Fin j → X) × F, ‖B p.1 p.2‖ ≤ K * (∏ i, ‖p.1 i‖) * ‖p.2‖ := by
    have hcl : IsClosed {p : (Fin j → X) × F | ‖B p.1 p.2‖ ≤ K * (∏ i, ‖p.1 i‖) * ‖p.2‖} := by
      apply isClosed_le
      · exact ((B.coe_continuous.comp continuous_fst).clm_apply continuous_snd).norm
      · refine Continuous.mul (Continuous.mul continuous_const ?_) continuous_snd.norm
        exact continuous_finsetProd _ fun i _ => ((continuous_apply i).comp continuous_fst).norm
    have hsub : (Set.pi Set.univ fun _ : Fin j => (C : Set X)) ×ˢ (CF : Set F) ⊆
        {p : (Fin j → X) × F | ‖B p.1 p.2‖ ≤ K * (∏ i, ‖p.1 i‖) * ‖p.2‖} := by
      rintro ⟨x, f⟩ ⟨hx, hf⟩
      exact hB (fun i => ⟨x i, hx i (Set.mem_univ i)⟩) ⟨f, hf⟩
    intro p
    have hp : p ∈ closure ((Set.pi Set.univ fun _ : Fin j => (C : Set X)) ×ˢ (CF : Set F)) := by
      rw [(dense_coreTuples hC hCF j).closure_eq]; exact Set.mem_univ p
    exact closure_minimal hsub hcl hp
  refine ContinuousMultilinearMap.opNorm_le_bound hK fun x => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f => ?_
  exact hall (x, f)

omit [CompleteSpace E] in
/-- The multilinear bound of a completed map on core tuples. -/
theorem norm_apply_core_le {j : ℕ}
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin j => X) (F →L[ℝ] E)) (h : Fin j → C) (f : CF) :
    ‖B (fun i => (h i : X)) f‖ ≤ ‖B‖ * (∏ i, ‖h i‖) * ‖f‖ := by
  refine ((B _).le_opNorm f).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact B.le_opNorm _

omit [CompleteSpace E] in
/-- Two continuous multilinear maps on the completions agreeing on core tuples are
equal (uniqueness of the slot completion). -/
theorem eq_of_core_agree (hC : Dense (C : Set X)) (hCF : Dense (CF : Set F)) {j : ℕ}
    (B₁ B₂ : ContinuousMultilinearMap ℝ (fun _ : Fin j => X) (F →L[ℝ] E))
    (h : ∀ (h : Fin j → C) (f : CF), B₁ (fun i => (h i : X)) f = B₂ (fun i => (h i : X)) f) :
    B₁ = B₂ := by
  have hle : ‖B₁ - B₂‖ ≤ 0 :=
    opNorm_le_of_core_bound hC hCF (B₁ - B₂) le_rfl fun h' f => by
      rw [sub_apply, sub_apply, h h' f, sub_self, norm_zero, zero_mul, zero_mul]
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

set_option maxHeartbeats 800000 in
/-- Slot completion, existence: a core-bounded multilinear core map extends to a
continuous multilinear map on the completions agreeing with it on core tuples. -/
theorem slotCompletion_exists (hC : Dense (C : Set X)) (hCF : Dense (CF : Set F)) :
    ∀ (j : ℕ) (A : MultilinearMap ℝ (fun _ : Fin j => C) (CF →ₗ[ℝ] E)) (K : ℝ), 0 ≤ K →
      (∀ (h : Fin j → C) (f : CF), ‖A h f‖ ≤ K * (∏ i, ‖h i‖) * ‖f‖) →
      ∃ B : ContinuousMultilinearMap ℝ (fun _ : Fin j => X) (F →L[ℝ] E),
        ∀ (h : Fin j → C) (f : CF), B (fun i => (h i : X)) f = A h f := by
  intro j
  induction j with
  | zero =>
    intro A K hK hA
    have hL : ∀ f : CF, ‖A 0 f‖ ≤ K * ‖f‖ := fun f => by
      have := hA 0 f
      simpa using this
    have hdense : DenseRange CF.subtypeL := hCF.denseRange_val
    have hunif : IsUniformInducing CF.subtypeL :=
      isUniformEmbedding_subtype_val.isUniformInducing
    refine ⟨ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => X)
      ((LinearMap.mkContinuous (A 0) K hL).extend CF.subtypeL), fun h f => ?_⟩
    show (LinearMap.mkContinuous (A 0) K hL).extend CF.subtypeL (CF.subtypeL f) = A h f
    rw [ContinuousLinearMap.extend_eq _ hdense hunif f]
    show A 0 f = A h f
    rw [Subsingleton.elim (0 : Fin 0 → C) h]
  | succ j ih =>
    intro A K hK hA
    have hcons : ∀ (a : C) (h : Fin j → C),
        (∏ i, ‖(Fin.cons a h : Fin (j + 1) → C) i‖) = ‖a‖ * ∏ i, ‖h i‖ := by
      intro a h
      rw [Fin.prod_univ_succ]
      simp [Fin.cons_zero, Fin.cons_succ]
    have hcurry : ∀ h₀ : C, ∃ B : ContinuousMultilinearMap ℝ (fun _ : Fin j => X) (F →L[ℝ] E),
        ∀ (h : Fin j → C) (f : CF), B (fun i => (h i : X)) f = A.curryLeft h₀ h f := by
      intro h₀
      refine ih (A.curryLeft h₀) (K * ‖h₀‖) (mul_nonneg hK (norm_nonneg _)) fun h f => ?_
      rw [MultilinearMap.curryLeft_apply]
      calc ‖A (Fin.cons h₀ h) f‖ ≤ K * (∏ i, ‖(Fin.cons h₀ h : Fin (j + 1) → C) i‖) * ‖f‖ :=
            hA _ f
        _ = K * ‖h₀‖ * (∏ i, ‖h i‖) * ‖f‖ := by rw [hcons]; ring
    choose Bf hBf using hcurry
    have hadd : ∀ a b : C, Bf (a + b) = Bf a + Bf b := fun a b =>
      eq_of_core_agree hC hCF _ _ fun h f => by
        rw [add_apply, add_apply, hBf, hBf, hBf]
        exact congrArg (fun L : MultilinearMap ℝ (fun _ : Fin j => C) (CF →ₗ[ℝ] E) => L h f)
          (map_add A.curryLeft a b)
    have hsmul : ∀ (c : ℝ) (a : C), Bf (c • a) = c • Bf a := fun c a =>
      eq_of_core_agree hC hCF _ _ fun h f => by
        rw [smul_apply, smul_apply, hBf, hBf]
        exact congrArg (fun L : MultilinearMap ℝ (fun _ : Fin j => C) (CF →ₗ[ℝ] E) => L h f)
          (map_smul A.curryLeft c a)
    have hbound : ∀ a : C, ‖Bf a‖ ≤ K * ‖a‖ := fun a =>
      opNorm_le_of_core_bound hC hCF (Bf a) (mul_nonneg hK (norm_nonneg _)) fun h f => by
        rw [hBf, MultilinearMap.curryLeft_apply]
        calc ‖A (Fin.cons a h) f‖ ≤ K * (∏ i, ‖(Fin.cons a h : Fin (j + 1) → C) i‖) * ‖f‖ :=
              hA _ f
          _ = K * ‖a‖ * (∏ i, ‖h i‖) * ‖f‖ := by rw [hcons]; ring
    let Bl : C →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j => X) (F →L[ℝ] E) :=
      LinearMap.mkContinuous { toFun := Bf, map_add' := hadd, map_smul' := hsmul } K hbound
    obtain ⟨Bx, key⟩ := dense_submodule_clm_extension
      (T := ContinuousMultilinearMap ℝ (fun _ : Fin j => X) (F →L[ℝ] E)) hC Bl
    refine ⟨ContinuousLinearMap.uncurryLeft (Ei := fun _ : Fin (j + 1) => X) Bx, fun h f => ?_⟩
    rw [ContinuousLinearMap.uncurryLeft_apply]
    show Bx ((h 0 : C) : X) (fun i => (Fin.tail h i : X)) f = A h f
    rw [key (h 0)]
    show Bf (h 0) (fun i => (Fin.tail h i : X)) f = A h f
    rw [hBf, MultilinearMap.curryLeft_apply, Fin.cons_self_tail]

/-- Slot completion (steps 1–2 of NG_F07): a multilinear core map with some core
bound extends to a continuous multilinear map on the completions agreeing with
it on core tuples, and the completed operator norm is at most every core
constant. -/
theorem slotCompletion (hC : Dense (C : Set X)) (hCF : Dense (CF : Set F)) (j : ℕ)
    (A : MultilinearMap ℝ (fun _ : Fin j => C) (CF →ₗ[ℝ] E))
    (hA : ∃ K : ℝ, ∀ (h : Fin j → C) (f : CF), ‖A h f‖ ≤ K * (∏ i, ‖h i‖) * ‖f‖) :
    ∃ B : ContinuousMultilinearMap ℝ (fun _ : Fin j => X) (F →L[ℝ] E),
      (∀ (h : Fin j → C) (f : CF), B (fun i => (h i : X)) f = A h f) ∧
      ∀ K : ℝ, 0 ≤ K → (∀ (h : Fin j → C) (f : CF), ‖A h f‖ ≤ K * (∏ i, ‖h i‖) * ‖f‖) →
        ‖B‖ ≤ K := by
  obtain ⟨K, hK⟩ := hA
  have hK' : ∀ (h : Fin j → C) (f : CF), ‖A h f‖ ≤ max K 0 * (∏ i, ‖h i‖) * ‖f‖ := fun h f =>
    (hK h f).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Finset.prod_nonneg fun i _ => norm_nonneg _)) (norm_nonneg _))
  obtain ⟨B, hB⟩ := slotCompletion_exists hC hCF j A (max K 0) (le_max_right _ _) hK'
  refine ⟨B, hB, fun K' hK'0 hA' => opNorm_le_of_core_bound hC hCF B hK'0 fun h f => ?_⟩
  rw [hB]
  exact hA' h f

end Slot

end Grad.FiniteBanachCalculus
