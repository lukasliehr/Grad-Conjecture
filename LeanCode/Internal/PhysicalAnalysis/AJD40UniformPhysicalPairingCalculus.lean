import AJD31CrossPacketUniformNorms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.AnnularKernelOrbit

section Pairing
variable {Context : Type*} {X D V : Context → Type*}
  [∀ context, NormedAddCommGroup (X context)] [∀ context, NormedSpace ℂ (X context)]
  [∀ context, NormedSpace ℝ (X context)] [∀ context, IsScalarTower ℝ ℂ (X context)]
  [∀ context, NormedAddCommGroup (D context)] [∀ context, InnerProductSpace ℂ (D context)]
  [∀ context, NormedAddCommGroup (V context)] [∀ context, NormedSpace ℝ (V context)]
  {budget : Context → ℕ → ℝ}
attribute [local instance] pairingRealInner
local instance pairedFamilyNormed (context : Context) : NormedAddCommGroup (X context →L[ℝ] V context →L[ℝ] ℝ) := inferInstance
local instance pairedFamilyRealNormed (context : Context) : NormedSpace ℝ (X context →L[ℝ] V context →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

theorem UniformCoordinateBound.pairedComplex
    {family : (context : Context) → OrbitParameter → X context →L[ℂ] D context}
    (bound : UniformCoordinateBound budget family) (smooth : ∀ context, ContDiff ℝ ∞ (family context))
    (test : (context : Context) → V context →L[ℝ] D context)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (testBound : ∀ context, ‖test context‖ ≤ constant) :
    UniformCoordinateBound budget (fun context tau => pairedComplexOperator (test context) (family context tau)) := by
  apply bound.map_bound (F := fun context => X context →L[ℝ] V context →L[ℝ] ℝ) smooth
    (fun context => pairedComplexOperator (X := X context) (D := D context) (V := V context) (test context)) constant nonnegative
  intro context mapping
  exact (pairedComplexOperator_bound (test context) mapping).trans
    (mul_le_mul_of_nonneg_right (testBound context) (norm_nonneg mapping))
end Pairing

section Restriction
variable {Context : Type*} {X W V : Context → Type*}
  [∀ context, NormedAddCommGroup (X context)] [∀ context, NormedSpace ℝ (X context)]
  [∀ context, NormedAddCommGroup (W context)] [∀ context, NormedSpace ℝ (W context)]
  [∀ context, NormedAddCommGroup (V context)] [∀ context, NormedSpace ℝ (V context)]
  {budget : Context → ℕ → ℝ}
local instance restrictedFamilyNormed (context : Context) : NormedAddCommGroup (X context →L[ℝ] V context →L[ℝ] ℝ) := inferInstance
local instance restrictedFamilyRealNormed (context : Context) : NormedSpace ℝ (X context →L[ℝ] V context →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

theorem UniformCoordinateBound.testRestriction
    {family : (context : Context) → OrbitParameter → X context →L[ℝ] W context →L[ℝ] ℝ}
    (bound : UniformCoordinateBound budget family) (smooth : ∀ context, ContDiff ℝ ∞ (family context))
    (inclusion : (context : Context) → V context →L[ℝ] W context)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (inclusionBound : ∀ context, ‖inclusion context‖ ≤ constant) :
    UniformCoordinateBound budget (fun context tau => operatorTestRestriction (inclusion context) (family context tau)) := by
  apply bound.map_bound (F := fun context => X context →L[ℝ] V context →L[ℝ] ℝ) smooth
    (fun context => operatorTestRestriction (X := X context) (W := W context) (V := V context) (inclusion context)) constant nonnegative
  intro context mapping
  exact (operatorTestRestriction_bound (inclusion context) mapping).trans
    (mul_le_mul_of_nonneg_right (inclusionBound context) (norm_nonneg mapping))
end Restriction
end Grad.AnnularCrossOrbit
