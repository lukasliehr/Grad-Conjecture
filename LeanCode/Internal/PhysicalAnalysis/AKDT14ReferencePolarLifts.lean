import AKDT13PolarCylinderCalculus

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalAmbient Grad.PhysicalFamily.SampledFullGeometry
open Grad.MainAssembly.PhysicalNormalHessian

/-- Literal cover points for the three real foliation coordinates. -/
def foliationCover (point : Vec) (membership : point ∈ foliationCylinder) : ClosedDisk × ℝ :=
  ((referenceFoliation (⟨point 0, membership⟩, (point 1 : CellCircle), (point 2 : CellCircle))).1, point 2)

theorem foliationCover_reference (point : Vec) (membership : point ∈ foliationCylinder) :
    referenceCover (foliationCover point membership) =
      referenceFoliation (⟨point 0, membership⟩, (point 1 : CellCircle), (point 2 : CellCircle)) := rfl

theorem foliationCover_point (point : Vec) (membership : point ∈ foliationCylinder) :
    referenceCoverPoint (foliationCover point membership) = polarCylinderLift point := by
  ext coordinate
  fin_cases coordinate <;>
    simp [referenceCoverPoint, foliationCover, referenceFoliation, polarDiskPoint, polarDiskValue,
      unitDiskCircle_coe, polarCylinderLift, coordinateDirection, vector]

theorem polarCylinderLift_mem (point : Vec) (membership : point ∈ foliationCylinder) :
    polarCylinderLift point ∈ cylinder := by
  rw [← foliationCover_point point membership]
  exact referenceCoverPoint_mem _

theorem polarCylinderLift_planar_norm (point : Vec) : ‖planarPart (polarCylinderLift point)‖ = |point 0| := by
  have identity : planarPart (polarCylinderLift point) = point 0 • unitDiskCircle (point 1 : CellCircle) := by
    rw [unitDiskCircle_coe]
    ext coordinate
    fin_cases coordinate <;> simp [polarCylinderLift, planarPart, vector]
  rw [identity, norm_smul, Real.norm_eq_abs, unitDiskCircle_norm, mul_one]

/-- The half-closed foliation cylinder has unique ambient derivatives even
on its radius-one boundary. -/
theorem uniqueDiffOn_foliationCylinder : UniqueDiffOn ℝ foliationCylinder := by
  have convex : Convex ℝ foliationCylinder := (convex_Ioc (0 : ℝ) 1).linear_preimage (vecCoordinateCLM 0).toLinearMap
  apply uniqueDiffOn_convex convex
  refine ⟨vector (1 / 2) 0 0, ?_⟩
  apply mem_interior_iff_mem_nhds.mpr
  have domainOpen : IsOpen {point : Vec | point 0 ∈ Ioo (0 : ℝ) 1} :=
    isOpen_Ioo.preimage (vecCoordinateCLM 0).continuous
  have pointIn : vector (1 / 2) 0 0 ∈ {point : Vec | point 0 ∈ Ioo (0 : ℝ) 1} := by norm_num [vector]
  exact Filter.mem_of_superset (domainOpen.mem_nhds pointIn) (fun point membership => ⟨membership.1, membership.2.le⟩)

end Grad.PhysicalGeometry
