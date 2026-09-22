import AJD33UniformOperatorComposition
import AJD14SameCompleteHighCrossResponseOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.AnnularKernelOrbit

section Pair
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def hilbertLeftInclusion : E →L[ℂ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℂ E F)

def hilbertRightInclusion : F →L[ℂ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℂ E F)

theorem hilbertLeftInclusion_norm : ‖hilbertLeftInclusion (E := E) (F := F)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro value
  have square := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (value, (0 : F)))
  change ‖WithLp.toLp 2 (value, (0 : F))‖ ^ 2 = ‖value‖ ^ 2 + ‖(0 : F)‖ ^ 2 at square
  change ‖WithLp.toLp 2 (value, (0 : F))‖ ≤ 1 * ‖value‖
  simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at square
  nlinarith [norm_nonneg (WithLp.toLp 2 (value, (0 : F))), norm_nonneg value]

theorem hilbertRightInclusion_norm : ‖hilbertRightInclusion (E := E) (F := F)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro value
  have square := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 ((0 : E), value))
  change ‖WithLp.toLp 2 ((0 : E), value)‖ ^ 2 = ‖(0 : E)‖ ^ 2 + ‖value‖ ^ 2 at square
  change ‖WithLp.toLp 2 ((0 : E), value)‖ ≤ 1 * ‖value‖
  simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] at square
  nlinarith [norm_nonneg (WithLp.toLp 2 ((0 : E), value)), norm_nonneg value]
end Pair

section Families
variable {Context : Type*} {X E F : Context → Type*}
  [∀ context, NormedAddCommGroup (X context)] [∀ context, NormedSpace ℂ (X context)]
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℂ (E context)]
  [∀ context, NormedAddCommGroup (F context)] [∀ context, NormedSpace ℂ (F context)]
  {budget : Context → ℕ → ℝ}

theorem UniformCoordinateBound.pairComplex
    {first : (context : Context) → OrbitParameter → X context →L[ℂ] E context}
    {second : (context : Context) → OrbitParameter → X context →L[ℂ] F context}
    (firstBound : UniformCoordinateBound budget first) (secondBound : UniformCoordinateBound budget second)
    (firstSmooth : ∀ context, ContDiff ℝ ∞ (first context))
    (secondSmooth : ∀ context, ContDiff ℝ ∞ (second context)) :
    UniformCoordinateBound budget (fun context tau => hilbertOperatorPair (first context tau) (second context tau)) := by
  have left := firstBound.postcomposeComplex firstSmooth
    (fun context => hilbertLeftInclusion (E := E context) (F := F context)) 1 (by norm_num)
    (fun _ => hilbertLeftInclusion_norm)
  have right := secondBound.postcomposeComplex secondSmooth
    (fun context => hilbertRightInclusion (E := E context) (F := F context)) 1 (by norm_num)
    (fun _ => hilbertRightInclusion_norm)
  have combined := left.add right
    (fun context => complexOperatorComposition_contDiff _ _ contDiff_const (firstSmooth context))
    (fun context => complexOperatorComposition_contDiff _ _ contDiff_const (secondSmooth context))
  have same (context : Context) (tau : OrbitParameter) :
      (hilbertLeftInclusion (E := E context) (F := F context)).comp (first context tau) +
        (hilbertRightInclusion (E := E context) (F := F context)).comp (second context tau) =
      hilbertOperatorPair (first context tau) (second context tau) := by
    apply ContinuousLinearMap.ext
    intro value
    change WithLp.toLp 2 ((first context tau value, 0) + (0, second context tau value)) = WithLp.toLp 2 (first context tau value, second context tau value)
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  simpa only [same] using combined
end Families

section Graph
variable {Context : Type*} {X E : Context → Type*}
  [∀ context, NormedAddCommGroup (X context)] [∀ context, NormedSpace ℂ (X context)]
  [∀ context, NormedAddCommGroup (E context)] [∀ context, InnerProductSpace ℂ (E context)]
  {budget : Context → ℕ → ℝ} (graph : (context : Context) → Submodule ℂ (E context))
  [∀ context, (graph context).HasOrthogonalProjection]

local instance graphFamilyNormed (context : Context) : NormedAddCommGroup (graph context) := inferInstance
local instance graphFamilyComplexNormed (context : Context) : NormedSpace ℂ (graph context) := inferInstance
local instance ambientOperatorNormed (context : Context) : NormedAddCommGroup (X context →L[ℂ] E context) := inferInstance
local instance ambientOperatorRealNormed (context : Context) : NormedSpace ℝ (X context →L[ℂ] E context) := ContinuousLinearMap.toNormedSpace
local instance graphOperatorNormed (context : Context) : NormedAddCommGroup (X context →L[ℂ] graph context) := inferInstance
local instance graphOperatorRealNormed (context : Context) : NormedSpace ℝ (X context →L[ℂ] graph context) := ContinuousLinearMap.toNormedSpace

theorem UniformCoordinateBound.graphComplex
    (family : (context : Context) → OrbitParameter → X context →L[ℂ] graph context)
    (smooth : ∀ context, ContDiff ℝ ∞ (fun tau => (graph context).subtypeL.comp (family context tau)))
    (bound : UniformCoordinateBound budget (fun context tau => (graph context).subtypeL.comp (family context tau))) :
    UniformCoordinateBound budget family := by
  let projection : (context : Context) → (X context →L[ℂ] E context) →L[ℝ] (X context →L[ℂ] graph context) :=
    fun context => graphOperatorProjection (X := X context) (graph context)
  have projectionBound (context : Context) (mapping : X context →L[ℂ] E context) :
      ‖projection context mapping‖ ≤ 1 * ‖mapping‖ :=
    (graphOperatorProjection_bound (graph context) mapping).trans_eq (one_mul _).symm
  have mapped := bound.map_bound (F := fun context => X context →L[ℂ] graph context) smooth projection 1 (by norm_num) projectionBound
  simpa only [projection, graphOperatorProjection_retract] using mapped
end Graph
end Grad.AnnularCrossOrbit
