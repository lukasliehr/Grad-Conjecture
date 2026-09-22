import AKDE13ConstructedTiltRemainder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 3500
open Set Filter
open scoped ContDiff Topology
namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.ClosedJets Grad.Constraints Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.OriginalParameterEvaluation Grad.PhysicalFamily Grad.NonlinearQuotient Grad.AxisSplit
open Grad.DiskExtension.Operator
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit

attribute [local irreducible] constructedPhysicalChart

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}
    {inverse : OriginalNewtonInverse neighborhood cellLength loss}

def constructedCellDomain (scale : OriginalNewtonScale inverse) : Set (OriginalFiniteParameter × (SpatialPlane × ℝ)) :=
  scale.openParameterDomain ×ˢ ({disk : SpatialPlane | ‖disk‖ < 4/3} ×ˢ Set.univ)

theorem constructedCellDomain_isOpen (scale : OriginalNewtonScale inverse) : IsOpen (constructedCellDomain scale) :=
  scale.openParameterDomain_isOpen.prod ((isOpen_lt continuous_norm continuous_const).prod isOpen_univ)

theorem constructedCellVector_joint_smooth (scale : OriginalNewtonScale inverse) (leftLaw : inverse.LeftLaw) :
    ContDiffOn ℝ ∞ (fun point : OriginalFiniteParameter × (SpatialPlane × ℝ) =>
      constructedCellVector scale point.1 point.2.1 point.2.2) (constructedCellDomain scale) := by
  have composition : ContDiff ℝ ∞ (fun point : OriginalFiniteParameter × (SpatialPlane × ℝ) =>
      (point.1,assembleSpatialCell point.2.1 point.2.2)) :=
    contDiff_fst.prodMk (assembleSpatialCellCLM.contDiff.comp contDiff_snd)
  have mapped : MapsTo (fun point : OriginalFiniteParameter × (SpatialPlane × ℝ) =>
      (point.1,assembleSpatialCell point.2.1 point.2.2)) (constructedCellDomain scale)
      (scale.openParameterDomain ×ˢ originalOpenCollar) := by
    intro point member
    exact ⟨member.1,by simpa only [originalOpenCollar,mem_ofPred_eq,planarPart_assembleSpatialCell] using member.2.1⟩
  have actual := (constructedRealFields_joint_smooth scale leftLaw).1.comp composition.contDiffOn mapped
  simpa only [Function.comp_def,constructedRealVector,constructedCellVector,realCellVector,
    originalRealExtendedField,originalCellField,originalProductField] using actual

theorem constructedCellPotential_joint_smooth (scale : OriginalNewtonScale inverse) (leftLaw : inverse.LeftLaw) :
    ContDiffOn ℝ ∞ (fun point : OriginalFiniteParameter × (SpatialPlane × ℝ) =>
      constructedCellPotential scale point.1 point.2.1 point.2.2) (constructedCellDomain scale) := by
  have composition : ContDiff ℝ ∞ (fun point : OriginalFiniteParameter × (SpatialPlane × ℝ) =>
      (point.1,assembleSpatialCell point.2.1 point.2.2)) :=
    contDiff_fst.prodMk (assembleSpatialCellCLM.contDiff.comp contDiff_snd)
  have mapped : MapsTo (fun point : OriginalFiniteParameter × (SpatialPlane × ℝ) =>
      (point.1,assembleSpatialCell point.2.1 point.2.2)) (constructedCellDomain scale)
      (scale.openParameterDomain ×ˢ originalOpenCollar) := by
    intro point member
    exact ⟨member.1,by simpa only [originalOpenCollar,mem_ofPred_eq,planarPart_assembleSpatialCell] using member.2.1⟩
  have actual := (EuclideanSpace.proj (0 : Fin 1)).contDiff.comp_contDiffOn
    ((constructedRealFields_joint_smooth scale leftLaw).2.comp composition.contDiffOn mapped)
  apply actual.congr
  intro point _
  simp [constructedCellPotential,realCellPotential,constructedRealPotential,originalRealExtendedField,
    originalScalarCell,originalCellField,originalProductField,physicalRealPart,EuclideanSpace.proj]

theorem constructedCellVector_joint_firstJet (scale : OriginalNewtonScale inverse) (leftLaw : inverse.LeftLaw)
    (point : OriginalFiniteParameter) (member : point ∈ scale.openParameterDomain) (direction : Fin 2) (cell : ℝ) :
    (fderiv ℝ (fun query : OriginalFiniteParameter × (SpatialPlane × ℝ) =>
      constructedCellVector scale query.1 query.2.1 query.2.2) (point,(0,cell)) (0,(spatialBasis direction,0))) 1 =
      constructedTilt scale point cell direction := by
  have insideDomain : (point,(0,cell)) ∈ constructedCellDomain scale := ⟨member,by norm_num,mem_univ _⟩
  have derivative := ((constructedCellVector_joint_smooth scale leftLaw).contDiffAt
    ((constructedCellDomain_isOpen scale).mem_nhds insideDomain)).differentiableAt (by simp)
  have inserted : HasFDerivAt (fun disk : SpatialPlane => (point,(disk,cell)))
      ((0 : SpatialPlane →L[ℝ] OriginalFiniteParameter).prod
        ((ContinuousLinearMap.id ℝ SpatialPlane).prod (0 : SpatialPlane →L[ℝ] ℝ))) 0 :=
    (hasFDerivAt_const point 0).prodMk ((hasFDerivAt_id (0 : SpatialPlane)).prodMk (hasFDerivAt_const cell 0))
  have law := congrArg (fun derivative : SpatialPlane →L[ℝ] EuclideanSpace ℝ (Fin 3) =>
    (derivative (spatialBasis direction)) 1) (derivative.hasFDerivAt.comp 0 inserted).fderiv
  exact law.symm.trans (constructedTilt_firstJet scale point member direction cell)

/-- Joint smoothness of the actual tilt follows from its genuine first
spatial jet on the fixed collar of the SAME constructed solution. -/
theorem constructedTilt_joint_smooth (scale : OriginalNewtonScale inverse) (leftLaw : inverse.LeftLaw) :
    ContDiffOn ℝ ∞ (fun point : OriginalFiniteParameter × ℝ => constructedTilt scale point.1 point.2)
      (scale.openParameterDomain ×ˢ Set.univ) := by
  rw [contDiffOn_piLp]
  intro direction
  have derivativeSmooth := ((contDiffOn_infty_iff_fderiv_of_isOpen
    (constructedCellDomain_isOpen scale)).mp (constructedCellVector_joint_smooth scale leftLaw)).2
  have insertion : ContDiff ℝ ∞ (fun point : OriginalFiniteParameter × ℝ => (point.1,((0 : SpatialPlane),point.2))) :=
    contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)
  have mapped : MapsTo (fun point : OriginalFiniteParameter × ℝ => (point.1,((0 : SpatialPlane),point.2)))
      (scale.openParameterDomain ×ˢ Set.univ) (constructedCellDomain scale) := by
    intro point member
    exact ⟨member.1,by norm_num,mem_univ _⟩
  have composed := derivativeSmooth.comp insertion.contDiffOn mapped
  have evaluated := (EuclideanSpace.proj (1 : Fin 3)).contDiff.comp_contDiffOn
    (composed.clm_apply (contDiffOn_const (c := (0,(spatialBasis direction,0)))))
  apply evaluated.congr
  intro point member
  exact (constructedCellVector_joint_firstJet scale leftLaw point.1 member.1 direction point.2).symm

theorem constructedNormalizedFactor_joint_smooth (scale : OriginalNewtonScale inverse) (leftLaw : inverse.LeftLaw) :
    ContDiffOn ℝ ∞ (fun point : OriginalFiniteParameter × ℝ => normalizedFactor (constructedTilt scale point.1 point.2))
      (scale.openParameterDomain ×ˢ Set.univ) := by
  apply (contDiffOn_const.sub ((constructedTilt_joint_smooth scale leftLaw).norm_sq ℝ |>.div_const 2)).sqrt
  intro point member
  have small := constructedTilt_bound scale point.1 member.1 point.2
  linarith

end Grad.OriginalCellFamily
