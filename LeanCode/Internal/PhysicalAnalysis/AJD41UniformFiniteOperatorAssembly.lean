import AJD36UniformClosedGraphAndPair
import AJD19CompleteActualCrossDataOrbits

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped ContDiff BigOperators
namespace Grad.AnnularCrossOrbit
open Grad.AnnularKernelOrbit Grad.AnnularOrbitGenerators Grad.AnnularInverseCalculus

section Pi
variable {Context Index : Type*} [Fintype Index] {E : Context → Type*}
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℝ (E context)]
  {budget : Context → ℕ → ℝ}

theorem UniformCoordinateBound.pi
    (family : Index → (context : Context) → OrbitParameter → E context)
    (bounds : ∀ index, UniformCoordinateBound budget (family index))
    (smooth : ∀ index context, ContDiff ℝ ∞ (family index context))
    (budgetNonnegative : ∀ context order, 0 ≤ budget context order) :
    UniformCoordinateBound budget (fun context tau index => family index context tau) := by
  intro axis order
  choose constant nonnegative estimate using fun index => bounds index axis order
  refine ⟨∑ index, constant index, Finset.sum_nonneg (fun index _ => nonnegative index), ?_⟩
  intro context base time
  have weightNonnegative := coordinateJetWeight_nonnegative (budget context) (budgetNonnegative context) order
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg (fun index _ => nonnegative index)) weightNonnegative)).2
  intro index
  have allSmooth : ContDiff ℝ ∞ (fun t : ℝ => fun index => family index context (base + t • axisVector axis)) :=
    contDiff_pi.mpr (fun index => (smooth index context).comp (contDiff_const.add (contDiff_id.smul contDiff_const)))
  have same := coefficient_iteratedDeriv (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Index => E context) index) _ allSmooth order time
  change (iteratedDeriv order (fun t : ℝ => fun index => family index context (base + t • axisVector axis)) time) index =
    iteratedDeriv order (fun t : ℝ => family index context (base + t • axisVector axis)) time at same
  rw [same]
  exact (estimate index context base time).trans
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => nonnegative i) (Finset.mem_univ index)) weightNonnegative)
end Pi

section Three
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem threeCollect_norm :
    ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => E)).symm.toContinuousLinearMap‖ ≤ 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro value
  have square := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => E) (WithLp.toLp 2 value)
  have bounded : ∑ index : Fin 3, ‖value index‖ ^ 2 ≤ ∑ _index : Fin 3, ‖value‖ ^ 2 :=
    Finset.sum_le_sum (fun index _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm value index) 2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at bounded
  change ‖WithLp.toLp 2 value‖ ^ 2 = ∑ index : Fin 3, ‖value index‖ ^ 2 at square
  change ‖WithLp.toLp 2 value‖ ≤ 3 * ‖value‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  norm_num at bounded
  nlinarith [sq_nonneg ‖value‖]
end Three

section Operators
variable {Context : Type*} {X E : Context → Type*}
  [∀ context, NormedAddCommGroup (X context)] [∀ context, NormedSpace ℂ (X context)]
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℂ (E context)]
  {budget : Context → ℕ → ℝ}

theorem UniformCoordinateBound.threeComplex
    (family : Fin 3 → (context : Context) → OrbitParameter → X context →L[ℂ] E context)
    (bounds : ∀ index, UniformCoordinateBound budget (family index))
    (smooth : ∀ index context, ContDiff ℝ ∞ (family index context))
    (budgetNonnegative : ∀ context order, 0 ≤ budget context order) :
    UniformCoordinateBound budget (fun context tau => piLpOperator (fun index : Fin 3 => family index context tau)) := by
  have all := UniformCoordinateBound.pi family bounds smooth budgetNonnegative
  have allSmooth (context : Context) : ContDiff ℝ ∞ (fun tau index => family index context tau) :=
    contDiff_pi.mpr (fun index => smooth index context)
  have assembled := all.map_bound allSmooth
    (F := fun context => X context →L[ℂ] Fin 3 → E context)
    (fun context => (piOperatorCLM (Index := Fin 3) (X := X context) (E := E context)).restrictScalars ℝ)
    1 (by norm_num) (fun context operators => by
      rw [one_mul]
      exact ContinuousLinearMap.norm_pi_le_of_le (norm_le_pi_norm operators) (norm_nonneg operators))
  apply assembled.postcomposeComplex
    (fun context => ((piOperatorCLM (Index := Fin 3) (X := X context) (E := E context)).restrictScalars ℝ).contDiff.comp (allSmooth context))
    (fun context => (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => E context)).symm.toContinuousLinearMap)
    3 (by norm_num) (fun _ => threeCollect_norm)
end Operators
end Grad.AnnularCrossOrbit
