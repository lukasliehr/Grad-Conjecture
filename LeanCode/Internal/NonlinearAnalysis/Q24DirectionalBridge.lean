import Q24FixedSeedMap
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open Filter
open scoped Topology ContDiff

namespace Grad.Q24Realization

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearQuotientBounds
open Grad.Constraints Grad.AxisCore Grad.SmoothingFamily Grad.ImplementationReadiness
open Grad.QuotientProjection

def jointCoreLinear (parameters : PhaseParameters) (grade : ℕ) :
    JointState parameters →ₗ[ℂ] JointAmbient parameters grade where
  toFun := jointCoreEmbed parameters grade
  map_add' first second := by
    apply (WithLp.equiv 1 _).injective
    apply Prod.ext
    · rfl
    · apply (WithLp.equiv 1 _).injective
      apply Prod.ext
      · exact map_add _ _ _
      · apply (WithLp.equiv 1 _).injective
        exact Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' scalar state := by
    apply (WithLp.equiv 1 _).injective
    apply Prod.ext
    · rfl
    · apply (WithLp.equiv 1 _).injective
      apply Prod.ext
      · exact map_smul _ _ _
      · apply (WithLp.equiv 1 _).injective
        exact Prod.ext (map_smul _ _ _) (map_smul _ _ _)

theorem coreRows_hasDerivAt (parameters : PhaseParameters) (grade : ℕ)
    (mapping : JointState parameters → QuotientRows parameters)
    (base direction : JointState parameters) (derivative : QuotientRows parameters)
    (genuine : IsJointRowsDirectionalDerivative mapping base direction derivative) :
    HasDerivAt (fun t : ℝ => quotientEta parameters grade (mapping (base + t • direction)))
      (quotientEta parameters grade derivative) 0 := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have limit := (genuine grade).const_mul 2
  simp only [mul_zero] at limit
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ limit
  filter_upwards with t
  have bound := quotientEta_norm_le_rows parameters grade
    (t⁻¹ • (mapping (base + t • direction) - mapping base) - derivative)
  change ‖((quotientEta parameters grade).restrictScalars ℝ)
    (t⁻¹ • (mapping (base + t • direction) - mapping base) - derivative)‖ ≤ _ at bound
  rw [map_sub, map_smul, map_sub] at bound
  rw [slope_def_module, sub_zero]
  change ‖t⁻¹ • (quotientEta parameters grade (mapping (base + t • direction)) -
    quotientEta parameters grade (mapping (base + (0 : ℝ) • direction))) -
    quotientEta parameters grade derivative‖ ≤ _
  rw [zero_smul ℝ direction, add_zero, ← Complex.ofReal_inv,
    Complex.coe_smul (t⁻¹) (mapping (base + (t : ℂ) • direction) - mapping base),
    Complex.coe_smul t direction]
  exact bound

section Identification

variable {C E F : Type*} [AddCommGroup C] [Module ℝ C]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Core directional towers append their newest direction, whereas Mathlib
prepends it. Reversing the tuple gives an exact identification without
postulating multilinearity or smoothness of the core tower. -/
theorem iteratedFDeriv_core_of_directional
    (embedding : C →ₗ[ℝ] E) (mapping : E → F) (domain : Set E)
    (openDomain : IsOpen domain) (smooth : ContDiffOn ℝ ∞ mapping domain)
    (tower : (order : ℕ) → C → (Fin order → C) → F)
    (zeroth : ∀ base, embedding base ∈ domain → ∀ directions,
      tower 0 base directions = mapping (embedding base))
    (step : ∀ order base (directions : Fin (order + 1) → C), embedding base ∈ domain →
      HasDerivAt (fun t : ℝ => tower order (base + t • directions (Fin.last order))
        (fun position => directions position.castSucc)) (tower (order + 1) base directions) 0)
    (order : ℕ) (base : C) (inside : embedding base ∈ domain) (directions : Fin order → C) :
    iteratedFDeriv ℝ order mapping (embedding base) (fun position => embedding (directions position)) =
      tower order base (fun position => directions position.rev) := by
  induction order generalizing base with
  | zero =>
    rw [iteratedFDeriv_zero_apply, zeroth base inside]
  | succ order ih =>
    have smoothAt := (smooth _ inside).contDiffAt (openDomain.mem_nhds inside)
    have derivativeAt := smoothAt.differentiableAt_iteratedFDeriv
      (m := order) (by exact_mod_cast (WithTop.coe_lt_top order : (order : ℕ∞) < ⊤))
    let tailTuple : Fin order → E := fun position => embedding (directions position.succ)
    have evaluated := (derivativeAt.continuousMultilinear_apply_const tailTuple).hasFDerivAt
    have line : HasDerivAt (fun t : ℝ => embedding base + t • embedding (directions 0))
        (embedding (directions 0)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (embedding (directions 0))).const_add (embedding base)
    have actualLine := evaluated.comp_hasDerivAt_of_eq 0 line (by simp)
    let reversed : Fin (order + 1) → C := fun position => directions position.rev
    have coreLine := step order base reversed inside
    have membership : ∀ᶠ t : ℝ in 𝓝 0, embedding (base + t • directions 0) ∈ domain := by
      have membership := line.continuousAt.preimage_mem_nhds
        (openDomain.mem_nhds (by simpa only [zero_smul, add_zero] using inside))
      change ∀ᶠ t : ℝ in 𝓝 0, embedding base + t • embedding (directions 0) ∈ domain at membership
      simpa only [map_add, map_smul] using membership
    have agree : (fun t : ℝ => iteratedFDeriv ℝ order mapping
        (embedding base + t • embedding (directions 0)) tailTuple) =ᶠ[𝓝 0]
      (fun t : ℝ => tower order (base + t • reversed (Fin.last order))
        (fun position => reversed position.castSucc)) := by
      filter_upwards [membership] with t ht
      rw [← map_smul, ← map_add]
      simpa only [tailTuple, reversed, Fin.rev_last, Fin.rev_castSucc] using
        ih (base + t • directions 0) ht (fun position => directions position.succ)
    have unique := actualLine.unique (coreLine.congr_of_eventuallyEq agree)
    rw [derivativeAt.iteratedFDeriv_succ_apply_left']
    exact unique

end Identification

end Grad.Q24Realization
