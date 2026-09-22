import MainStatement
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FinCases

noncomputable section

open Set
open scoped ContDiff Topology

namespace Grad.MainTarget.SemanticBridges

def planarLinear : Vec →ₗ[ℝ] Plane where
  toFun := planarPart
  map_add' first second := by
    ext index
    fin_cases index <;> rfl
  map_smul' scalar point := by
    ext index
    fin_cases index <;> rfl

theorem continuous_planarPart : Continuous planarPart :=
  planarLinear.continuous_of_finiteDimensional

theorem convex_cylinder : Convex ℝ cylinder := by
  have description : cylinder = planarLinear ⁻¹' Metric.closedBall 0 1 := by
    ext point
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right]
    rfl
  rw [description]
  exact (convex_closedBall (0 : Plane) (1 : ℝ)).linear_preimage planarLinear

theorem zero_mem_interior_cylinder : (0 : Vec) ∈ interior cylinder := by
  apply mem_interior_iff_mem_nhds.mpr
  have openInterior : IsOpen {point : Vec | ‖planarPart point‖ < 1} :=
    isOpen_lt continuous_planarPart.norm continuous_const
  have zeroInside : (0 : Vec) ∈ {point : Vec | ‖planarPart point‖ < 1} := by
    change ‖planarLinear 0‖ < 1
    simp
  exact Filter.mem_of_superset (openInterior.mem_nhds zeroInside)
    (fun point (membership : ‖planarPart point‖ < 1) =>
      show point ∈ cylinder from membership.le)

theorem uniqueDiffOn_cylinder : UniqueDiffOn ℝ cylinder :=
  uniqueDiffOn_convex convex_cylinder ⟨0, zero_mem_interior_cylinder⟩

section LocalExtensions

variable {Domain Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem localExtensions_contDiffOn {regularity : Regularity}
    {mapping : Domain → Target} {domain : Set Domain}
    (extensions : HasLocalExtensions regularity mapping domain) :
    ContDiffOn ℝ regularity.order mapping domain := by
  apply contDiffOn_of_locally_contDiffOn
  intro point membership
  obtain ⟨neighborhood, openNeighborhood, pointInside, extension, smoothExtension, agreement⟩ :=
    extensions point membership
  refine ⟨neighborhood, openNeighborhood, pointInside, ?_⟩
  exact (smoothExtension.mono inter_subset_right).congr
    (fun _ argumentInside => (agreement ⟨argumentInside.2, argumentInside.1⟩).symm)

theorem localExtension_iteratedFDerivWithin {regularity : Regularity}
    {mapping extension : Domain → Target} {domain neighborhood : Set Domain}
    {point : Domain} {order : ℕ}
    (uniqueDerivatives : UniqueDiffOn ℝ domain)
    (pointInDomain : point ∈ domain) (openNeighborhood : IsOpen neighborhood)
    (pointInside : point ∈ neighborhood)
    (smoothExtension : ContDiffOn ℝ regularity.order extension neighborhood)
    (agreement : EqOn extension mapping (neighborhood ∩ domain))
    (admitted : regularity.admits order) :
    iteratedFDerivWithin ℝ order mapping domain point =
      iteratedFDeriv ℝ order extension point := by
  calc
    iteratedFDerivWithin ℝ order mapping domain point =
        iteratedFDerivWithin ℝ order mapping (domain ∩ neighborhood) point :=
      (iteratedFDerivWithin_inter_open openNeighborhood pointInside).symm
    _ = iteratedFDerivWithin ℝ order extension (domain ∩ neighborhood) point :=
      iteratedFDerivWithin_congr (s := domain ∩ neighborhood)
        (fun _ argumentInside => (agreement ⟨argumentInside.2, argumentInside.1⟩).symm)
        ⟨pointInDomain, pointInside⟩ order
    _ = iteratedFDerivWithin ℝ order extension domain point :=
      iteratedFDerivWithin_inter_open openNeighborhood pointInside
    _ = iteratedFDeriv ℝ order extension point :=
      iteratedFDerivWithin_eq_iteratedFDeriv uniqueDerivatives
        ((smoothExtension.contDiffAt (openNeighborhood.mem_nhds pointInside)).of_le admitted)
        pointInDomain

theorem localExtension_fderivWithin {regularity : Regularity}
    {mapping extension : Domain → Target} {domain neighborhood : Set Domain}
    {point : Domain}
    (uniqueDerivatives : UniqueDiffOn ℝ domain)
    (pointInDomain : point ∈ domain) (openNeighborhood : IsOpen neighborhood)
    (pointInside : point ∈ neighborhood)
    (smoothExtension : ContDiffOn ℝ regularity.order extension neighborhood)
    (agreement : EqOn extension mapping (neighborhood ∩ domain))
    (positiveOrder : regularity.order ≠ 0) :
    fderivWithin ℝ mapping domain point = fderiv ℝ extension point := by
  have locallyEqual : mapping =ᶠ[𝓝[domain] point] extension := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (openNeighborhood.mem_nhds pointInside),
      self_mem_nhdsWithin] with argument inNeighborhood inDomain
    exact (agreement ⟨inNeighborhood, inDomain⟩).symm
  exact (locallyEqual.fderivWithin_eq_of_mem pointInDomain).trans
    (((smoothExtension.contDiffAt (openNeighborhood.mem_nhds pointInside)).differentiableAt
      positiveOrder).fderivWithin (uniqueDerivatives point pointInDomain))

end LocalExtensions

section Cylinder

variable {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem regularity_contDiffOn {regularity : Regularity} {mapping : Reference → Target}
    (regularMapping : HasRegularity regularity mapping) :
    ContDiffOn ℝ regularity.order (periodicLift mapping) cylinder :=
  localExtensions_contDiffOn regularMapping

theorem regularity_continuousOn_jets {regularity : Regularity}
    {mapping : Reference → Target} (regularMapping : HasRegularity regularity mapping)
    {order : ℕ} (admitted : regularity.admits order) :
    ContinuousOn (iteratedFDerivWithin ℝ order (periodicLift mapping) cylinder) cylinder :=
  (regularity_contDiffOn regularMapping).continuousOn_iteratedFDerivWithin admitted
    uniqueDiffOn_cylinder

theorem cylinder_jet_eq_extension {regularity : Regularity} {mapping : Reference → Target}
    {extension : Vec → Target} {neighborhood : Set Vec} {point : Vec} {order : ℕ}
    (pointInCylinder : point ∈ cylinder) (openNeighborhood : IsOpen neighborhood)
    (pointInside : point ∈ neighborhood)
    (smoothExtension : ContDiffOn ℝ regularity.order extension neighborhood)
    (agreement : EqOn extension (periodicLift mapping) (neighborhood ∩ cylinder))
    (admitted : regularity.admits order) :
    iteratedFDerivWithin ℝ order (periodicLift mapping) cylinder point =
      iteratedFDeriv ℝ order extension point :=
  localExtension_iteratedFDerivWithin uniqueDiffOn_cylinder pointInCylinder openNeighborhood
    pointInside smoothExtension agreement admitted

theorem cylinder_extension_jets_independent {regularity : Regularity}
    {mapping : Reference → Target} {firstExtension secondExtension : Vec → Target}
    {firstNeighborhood secondNeighborhood : Set Vec} {point : Vec} {order : ℕ}
    (pointInCylinder : point ∈ cylinder)
    (firstOpen : IsOpen firstNeighborhood) (pointInFirst : point ∈ firstNeighborhood)
    (firstSmooth : ContDiffOn ℝ regularity.order firstExtension firstNeighborhood)
    (firstAgreement : EqOn firstExtension (periodicLift mapping) (firstNeighborhood ∩ cylinder))
    (secondOpen : IsOpen secondNeighborhood) (pointInSecond : point ∈ secondNeighborhood)
    (secondSmooth : ContDiffOn ℝ regularity.order secondExtension secondNeighborhood)
    (secondAgreement : EqOn secondExtension (periodicLift mapping) (secondNeighborhood ∩ cylinder))
    (admitted : regularity.admits order) :
    iteratedFDeriv ℝ order firstExtension point = iteratedFDeriv ℝ order secondExtension point :=
  (cylinder_jet_eq_extension pointInCylinder firstOpen pointInFirst firstSmooth firstAgreement
    admitted).symm.trans
      (cylinder_jet_eq_extension pointInCylinder secondOpen pointInSecond secondSmooth
        secondAgreement admitted)

theorem cylinder_immersion_iff_extension {regularity : Regularity}
    {mapping : Reference → Target} {extension : Vec → Target} {neighborhood : Set Vec}
    {point : Vec} (pointInCylinder : point ∈ cylinder)
    (openNeighborhood : IsOpen neighborhood) (pointInside : point ∈ neighborhood)
    (smoothExtension : ContDiffOn ℝ regularity.order extension neighborhood)
    (agreement : EqOn extension (periodicLift mapping) (neighborhood ∩ cylinder))
    (positiveOrder : regularity.order ≠ 0) :
    Function.Injective (fderivWithin ℝ (periodicLift mapping) cylinder point) ↔
      Function.Injective (fderiv ℝ extension point) := by
  rw [localExtension_fderivWithin uniqueDiffOn_cylinder pointInCylinder openNeighborhood
    pointInside smoothExtension agreement positiveOrder]

theorem target_jet_eq_extension {regularity : Regularity} {mapping : Reference → Target}
    {extension : Vec → Target} {neighborhood : Set Vec}
    (point : fundamentalCylinder) (order : {order : ℕ // regularity.admits order})
    (openNeighborhood : IsOpen neighborhood) (pointInside : point.val ∈ neighborhood)
    (smoothExtension : ContDiffOn ℝ regularity.order extension neighborhood)
    (agreement : EqOn extension (periodicLift mapping) (neighborhood ∩ cylinder)) :
    UniformFun.toFun (jets regularity mapping order) point =
      iteratedFDeriv ℝ order.val extension point.val :=
  cylinder_jet_eq_extension point.property.1 openNeighborhood pointInside smoothExtension
    agreement order.property

theorem cylinder_jets_ignore_exterior {mapping : Reference → Target}
    {alternative : Vec → Target}
    (agreement : EqOn alternative (periodicLift mapping) cylinder)
    {point : Vec} (pointInCylinder : point ∈ cylinder) (order : ℕ) :
    iteratedFDerivWithin ℝ order alternative cylinder point =
      iteratedFDerivWithin ℝ order (periodicLift mapping) cylinder point :=
  iteratedFDerivWithin_congr agreement pointInCylinder order

end Cylinder

end Grad.MainTarget.SemanticBridges
