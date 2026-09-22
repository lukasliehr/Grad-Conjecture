import AJD23OneVariableInverseBounds
import AJD26UniformCoordinateCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.AnnularKernelOrbit Grad.AnnularInverseCalculus

variable {Context 𝕜 : Type*} [RCLike 𝕜] {E F : Context → Type*}
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace 𝕜 (E context)]
  [∀ context, NormedSpace ℝ (E context)] [∀ context, IsScalarTower ℝ 𝕜 (E context)]
  [∀ context, NormedAddCommGroup (F context)] [∀ context, NormedSpace 𝕜 (F context)]
  [∀ context, NormedSpace ℝ (F context)] [∀ context, IsScalarTower ℝ 𝕜 (F context)]
  [∀ context, CompleteSpace (E context)]
  {budget : Context → ℕ → ℝ}

/-- A uniformly bounded SAME two-sided inverse inherits the genuine pure
coordinate one-high tower from its forward operator on the unchanged contexts. -/
theorem UniformCoordinateBound.sameInverse
    (forward : (context : Context) → OrbitParameter → E context →L[𝕜] F context)
    (inverse : (context : Context) → OrbitParameter → F context →L[𝕜] E context)
    (bound : UniformCoordinateBound budget forward)
    (smooth : ∀ context, ContDiff ℝ ∞ (forward context))
    (right : ∀ context point, (forward context point).comp (inverse context point) = ContinuousLinearMap.id 𝕜 (F context))
    (left : ∀ context point, (inverse context point).comp (forward context point) = ContinuousLinearMap.id 𝕜 (E context))
    (inverseBound : ℝ) (inverseNonnegative : 0 ≤ inverseBound)
    (inverseEstimate : ∀ context point, ‖inverse context point‖ ≤ inverseBound)
    (budgetNonnegative : ∀ context order, 0 ≤ budget context order)
    (budgetMonotone : ∀ context, Monotone (budget context))
    (pair : ℕ → ℝ) (pairNonnegative : ∀ order, 0 ≤ pair order)
    (pairEstimate : ∀ context a b, budget context a * budget context b ≤ pair (a + b) * budget context (a + b)) :
    UniformCoordinateBound budget inverse := by
  intro axis order
  choose jetConstant jetNonnegative jetEstimate using bound axis
  by_cases zero : order = 0
  · subst order
    refine ⟨inverseBound, inverseNonnegative, ?_⟩
    intro context base time
    simpa only [iteratedDeriv_zero, coordinateJetWeight, ↓reduceIte, mul_one] using inverseEstimate context (base + time • axisVector axis)
  · let constant := (inverseDerivativeWord (List.replicate order false)).bound inverseBound
      (fun angular cell => jetConstant (angular + cell)) pair
    have constantNonnegative : 0 ≤ constant :=
      (inverseDerivativeWord (List.replicate order false)).bound_nonnegative inverseBound _ pair
        inverseNonnegative (fun angular cell => jetNonnegative (angular + cell)) pairNonnegative
    refine ⟨constant, constantNonnegative, ?_⟩
    intro context base time
    have curveSmooth : ContDiff ℝ ∞ (fun t : ℝ => forward context (base + t • axisVector axis)) :=
      (smooth context).comp (contDiff_const.add (contDiff_id.smul contDiff_const))
    have positiveJets (index : ℕ) (positive : 0 < index) (point : ℝ) :
        ‖iteratedDeriv index (fun t : ℝ => forward context (base + t • axisVector axis)) point‖ ≤
          jetConstant index * budget context index := by
      simpa only [coordinateJetWeight, if_neg (Nat.ne_of_gt positive)] using jetEstimate index context base point
    have actual := iteratedDeriv_sameInverse_oneHigh
      (fun t : ℝ => forward context (base + t • axisVector axis))
      (fun t : ℝ => inverse context (base + t • axisVector axis)) curveSmooth
      (fun t => right context (base + t • axisVector axis))
      (fun t => left context (base + t • axisVector axis))
      (budget context) (budgetNonnegative context) (budgetMonotone context)
      inverseBound jetConstant pair inverseNonnegative jetNonnegative pairNonnegative
      (fun t => inverseEstimate context (base + t • axisVector axis)) positiveJets (pairEstimate context)
      order (Nat.pos_of_ne_zero zero) time
    simpa only [coordinateJetWeight, if_neg zero] using actual
end Grad.AnnularCrossOrbit
