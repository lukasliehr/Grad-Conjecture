import Q23MixedInnerZeroth

noncomputable section

set_option maxRecDepth 5000
set_option maxHeartbeats 3200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Seed

/-- Iterated Fréchet derivatives, evaluated on fixed old directions and
restricted to an affine real line, differentiate to the next derivative with
Mathlib's newest-first `curryLeft` convention. -/
theorem q23IteratedFDeriv_line_hasFDerivAt
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mapping : P → E) (domain : Set P) (openDomain : IsOpen domain)
    (smooth : ContDiffOn ℝ ∞ mapping domain)
    (order : ℕ) (point : P) (inside : point ∈ domain)
    (oldDirections : Fin order → P) (newDirection : P) :
    HasFDerivAt
      (fun t : ℝ => iteratedFDeriv ℝ order mapping
        (point + t • newDirection) oldDirections)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight
        (iteratedFDeriv ℝ (order + 1) mapping point
          (Fin.cons newDirection oldDirections))) 0 := by
  let evaluation := ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin order => P) E oldDirections
  have smoothAt := smooth.contDiffAt (openDomain.mem_nhds inside)
  have derivativeAt : HasFDerivAt (iteratedFDeriv ℝ order mapping)
      (iteratedFDeriv ℝ (order + 1) mapping point).curryLeft point := by
    have differentiable := smoothAt.differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl order)
    have result := differentiable.hasFDerivAt
    rw [fderiv_iteratedFDeriv, Function.comp_apply] at result
    exact result
  have evaluated := evaluation.hasFDerivAt.comp point derivativeAt
  let lineMap : ℝ →L[ℝ] P :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight newDirection
  have lineDerivative : HasFDerivAt (fun t : ℝ => point + lineMap t) lineMap 0 := by
    have raw := (hasFDerivAt_const (x := (0 : ℝ)) point).add lineMap.hasFDerivAt
    exact raw.congr_fderiv (zero_add lineMap)
  have evaluatedAtLine : HasFDerivAt
      (evaluation ∘ iteratedFDeriv ℝ order mapping)
      (evaluation.comp (iteratedFDeriv ℝ (order + 1) mapping point).curryLeft)
      (point + lineMap 0) := by
    simpa [lineMap] using evaluated
  have composed := evaluatedAtLine.comp 0 lineDerivative
  have derivativeEquality :
      (evaluation.comp
          (iteratedFDeriv ℝ (order + 1) mapping point).curryLeft).comp lineMap =
        (ContinuousLinearMap.id ℝ ℝ).smulRight
          (iteratedFDeriv ℝ (order + 1) mapping point
            (Fin.cons newDirection oldDirections)) := by
    apply ContinuousLinearMap.ext
    intro scalar
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply]
    dsimp [evaluation, lineMap]
    let derivative := iteratedFDeriv ℝ (order + 1) mapping point
    change (derivative.curryLeft (scalar • newDirection)) oldDirections =
      scalar • (derivative.curryLeft newDirection) oldDirections
    rw [map_smul, smul_apply]
  exact (composed.congr_fderiv derivativeEquality).congr_of_eventuallyEq
    (Eventually.of_forall fun _ => rfl)

theorem q23IteratedFDeriv_line_genuine
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (mapping : P → E) (domain : Set P) (openDomain : IsOpen domain)
    (smooth : ContDiffOn ℝ ∞ mapping domain)
    (order : ℕ) (point : P) (inside : point ∈ domain)
    (oldDirections : Fin order → P) (newDirection : P) :
    Tendsto (fun t : ℝ =>
      ‖(((t : ℂ))⁻¹ •
          (iteratedFDeriv ℝ order mapping (point + t • newDirection) oldDirections -
            iteratedFDeriv ℝ order mapping point oldDirections)) -
        iteratedFDeriv ℝ (order + 1) mapping point
          (Fin.cons newDirection oldDirections)‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have realLimit := hasFDerivAt_real_quotient _ _
    (q23IteratedFDeriv_line_hasFDerivAt mapping domain openDomain smooth
      order point inside oldDirections newDirection)
  refine realLimit.congr' (Eventually.of_forall fun t => ?_)
  rw [zero_smul, add_zero, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  change ‖((t⁻¹ : ℝ) : ℂ) • _ - _‖ = ‖((t : ℂ)⁻¹) • _ - _‖
  rw [Complex.ofReal_inv]

/-- Transfer of an actual Banach-space derivative tower to an isometrically
embedded smooth core, in one chosen core seminorm. -/
theorem q23CoreTower_genuine_of_actual
    {P E Core : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [AddCommGroup Core] [Module ℂ Core]
    (mapping : P → E) (domain : Set P) (openDomain : IsOpen domain)
    (smooth : ContDiffOn ℝ ∞ mapping domain)
    (embedding : Core →ₗ[ℂ] E) (coreNorm : Core → ℝ)
    (norm_eq : ∀ value, ‖embedding value‖ = coreNorm value)
    (tower : (order : ℕ) → P → (Fin order → P) → Core)
    (agrees : ∀ (order : ℕ) (point : P), point ∈ domain →
      ∀ directions, iteratedFDeriv ℝ order mapping point directions =
        embedding (tower order point directions))
    (order : ℕ) (point : P) (inside : point ∈ domain)
    (oldDirections : Fin order → P) (newDirection : P) :
    Tendsto (fun t : ℝ => coreNorm
      ((((t : ℂ))⁻¹ •
          (tower order (point + t • newDirection) oldDirections -
            tower order point oldDirections)) -
        tower (order + 1) point (Fin.cons newDirection oldDirections)))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have actual := q23IteratedFDeriv_line_genuine mapping domain openDomain smooth
    order point inside oldDirections newDirection
  have lineContinuous : ContinuousAt (fun t : ℝ => point + t • newDirection) 0 := by
    fun_prop
  have near : ∀ᶠ t : ℝ in 𝓝 0, point + t • newDirection ∈ domain :=
    lineContinuous.preimage_mem_nhds (openDomain.mem_nhds (by simpa using inside))
  refine actual.congr' ?_
  filter_upwards [near.filter_mono nhdsWithin_le_nhds] with t movedInside
  rw [agrees order (point + t • newDirection) movedInside oldDirections,
    agrees order point inside oldDirections,
    agrees (order + 1) point inside (Fin.cons newDirection oldDirections),
    ← map_sub, ← map_smul, ← map_sub, norm_eq]

end Grad.NonlinearQuotientBounds
