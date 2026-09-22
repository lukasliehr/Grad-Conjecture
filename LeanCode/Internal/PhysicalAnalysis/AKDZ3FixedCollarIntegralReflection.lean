import AKDX4FixedCartesianEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.OriginalCollarNorm
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift Grad.Constraints
open Grad.DiskExtension.Operator

/-- Fubini for the SAME fixed closed collar; endpoints have zero measure. -/
theorem fixedCollarIntegral_swap (lower : ℝ) (bounded : lower<1)
    (function : ℝ×ℝ→ℝ) (continuousFunction : Continuous function) :
    (∫ time in (0:ℝ)..(1-lower),∫ angle in -Real.pi..Real.pi,function (time,angle))=
      fixedCollarIntegral lower function := by
  have integrable : Integrable function
      ((volume.restrict (Icc (0:ℝ) (1-lower))).prod (volume.restrict (Icc (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact continuousFunction.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have swap := integral_integral_swap (f:=fun time angle : ℝ => function (time,angle)) integrable
  unfold fixedCollarIntegral
  simp_rw [intervalIntegral.integral_of_le (by linarith : (0:ℝ)≤1-lower),
    intervalIntegral.integral_of_le (neg_lt_self Real.pi_pos).le]
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
  simp_rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc]
  exact swap

/-- Time to radius is the literal reflection r=1-t on the unchanged collar. -/
theorem fixedCollarIntegral_reflection (lower : ℝ) (bounded : lower<1)
    (function : ℝ×ℝ→ℝ) (continuousFunction : Continuous function) :
    fixedCollarIntegral lower (fun point => function (1-point.1,point.2))=
      ∫ radius in lower..1,∫ angle in -Real.pi..Real.pi,function (radius,angle) := by
  have reflectedContinuous : Continuous (fun point : ℝ×ℝ => function (1-point.1,point.2)) :=
    continuousFunction.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)
  rw [←fixedCollarIntegral_swap lower bounded (fun point => function (1-point.1,point.2)) reflectedContinuous]
  have substitution := intervalIntegral.integral_comp_sub_left
    (fun radius => ∫ angle in -Real.pi..Real.pi,function (radius,angle)) (a:=(0:ℝ)) (b:=1-lower) 1
  simpa only [sub_zero,show (1:ℝ)-(1-lower)=lower by ring] using substitution

/-- Negating the radial coordinate is an exact isometry for the product norm. -/
def radialSignIsometry : (ℝ×ℝ) ≃ₗᵢ[ℝ] (ℝ×ℝ) where
  toFun point := (-point.1,point.2)
  invFun point := (-point.1,point.2)
  left_inv point := by ext <;> simp
  right_inv point := by ext <;> simp
  map_add' first second := by ext <;> simp; ring
  map_smul' scalar point := by ext <;> simp
  norm_map' point := by simp [Prod.norm_def]

theorem radialSignIsometry_apply (point : ℝ×ℝ) : radialSignIsometry point=(-point.1,point.2) := rfl

/-- The time/radius reflection preserves every full polar tensor norm. -/
theorem reflectedPolarTensor_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : ℝ×ℝ→E) (order : ℕ) (point : ℝ×ℝ) :
    ‖iteratedFDeriv ℝ order (fun source => field (1-source.1,source.2)) point‖=
      ‖iteratedFDeriv ℝ order field (1-point.1,point.2)‖ := by
  have representation : (fun source : ℝ×ℝ => field (1-source.1,source.2))=
      (fun source : ℝ×ℝ => field (source+(1,0))) ∘ radialSignIsometry := by
    funext source
    simp only [Function.comp_apply,radialSignIsometry_apply,Prod.mk_add_mk,add_zero]
    congr 2
    ring
  rw [representation,radialSignIsometry.norm_iteratedFDeriv_comp_right,iteratedFDeriv_comp_add_right]
  simp only [radialSignIsometry_apply,Prod.mk_add_mk,add_zero]
  congr 3
  ring

end Grad.OriginalCollarNorm
