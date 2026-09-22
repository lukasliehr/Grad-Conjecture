import AKDE16CompactParameterMeanValue

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
open Set
open scoped ContDiff Topology
namespace Grad.OriginalCellFamily
variable {P X Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def spatialDerivativePacket (order : ℕ) (field : P × X → Y) (point : P × X) :
    ContinuousMultilinearMap ℝ (fun _ : Fin order => X) Y :=
  iteratedFDeriv ℝ order (fun spatial => field (point.1,spatial)) point.2

/-- The packet contains the actual spatial derivatives at fixed parameter;
its smoothness is obtained by restriction of the genuine joint derivative. -/
theorem spatialDerivativePacket_same (domain : Set (P × X)) (openDomain : IsOpen domain)
    (field : P × X → Y) (smooth : ContDiffOn ℝ ∞ field domain) (order : ℕ)
    (point : P × X) (member : point ∈ domain) :
    spatialDerivativePacket order field point =
      (iteratedFDeriv ℝ order field point).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ P X) := by
  let translated := fun query : P × X => (point.1,0) + query
  let shifted := translated ⁻¹' domain
  have shiftedOpen : IsOpen shifted := openDomain.preimage (continuous_const.add continuous_id)
  have shiftedSmooth : ContDiffOn ℝ ∞ (field ∘ translated) shifted :=
    smooth.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ inside => inside)
  have imageInside : (ContinuousLinearMap.inr ℝ P X) point.2 ∈ shifted := by
    simpa [shifted,translated] using member
  have preimageOpen : IsOpen ((ContinuousLinearMap.inr ℝ P X) ⁻¹' shifted) :=
    shiftedOpen.preimage (ContinuousLinearMap.inr ℝ P X).continuous
  have chain := (ContinuousLinearMap.inr ℝ P X).iteratedFDerivWithin_comp_right
    shiftedSmooth shiftedOpen.uniqueDiffOn preimageOpen.uniqueDiffOn imageInside
    (show (order : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDerivWithin_of_isOpen order preimageOpen imageInside,
    iteratedFDerivWithin_of_isOpen order shiftedOpen imageInside] at chain
  have translation := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := field) order (point.1,0) ((0,point.2) : P × X)
  change iteratedFDeriv ℝ order (field ∘ translated) (0,point.2) = _ at translation
  simp only [ContinuousLinearMap.inr_apply] at chain
  rw [translation] at chain
  simpa only [spatialDerivativePacket,Function.comp_def,translated,ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk,add_zero,zero_add,Prod.mk.eta] using chain

theorem spatialDerivativePacket_joint_smooth (domain : Set (P × X)) (openDomain : IsOpen domain)
    (field : P × X → Y) (smooth : ContDiffOn ℝ ∞ field domain) (order : ℕ) :
    ContDiffOn ℝ ∞ (spatialDerivativePacket order field) domain := by
  have joint : ContDiffOn ℝ ∞ (iteratedFDeriv ℝ order field) domain := by
    apply openDomain.contDiffOn_iff.mpr
    intro point member
    exact (smooth.contDiffAt (openDomain.mem_nhds member)).iteratedFDeriv_right (m := ∞) (i := order) (by norm_cast)
  have restricted := (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin order => ContinuousLinearMap.inr ℝ P X)).contDiff.comp_contDiffOn joint
  apply restricted.congr
  intro point member
  exact spatialDerivativePacket_same domain openDomain field smooth order point member

end Grad.OriginalCellFamily
