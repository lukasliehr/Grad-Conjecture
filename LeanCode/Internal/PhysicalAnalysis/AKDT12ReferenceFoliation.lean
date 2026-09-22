import AKDT11PolarDiskHomeomorph

noncomputable section
open Set
open scoped Topology

namespace Grad.PhysicalGeometry
open Grad.MainTarget

local instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- The explicit radius and two quotient angles of the original reference
cylinder, with radius one retained. -/
def referenceFoliation (argument : FoliationDomain) : Reference :=
  ((polarDiskPoint (argument.1, argument.2.1)).val, argument.2.2)

theorem referenceFoliation_isEmbedding : Topology.IsEmbedding referenceFoliation := by
  let rearrange : FoliationDomain ≃ₜ PolarDiskDomain × CellCircle :=
    (Homeomorph.prodAssoc (Ioc (0 : ℝ) 1) CellCircle CellCircle).symm
  let polar : PolarDiskDomain × CellCircle ≃ₜ PuncturedDisk × CellCircle :=
    polarDiskHomeomorph.prodCongr (Homeomorph.refl CellCircle)
  have projection : Topology.IsEmbedding (fun argument : PuncturedDisk × CellCircle => (argument.1.val, argument.2)) :=
    Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.id
  exact projection.comp (polar.isEmbedding.comp rearrange.isEmbedding)

theorem referenceFoliation_range : range referenceFoliation = {point : Reference | point.1.val ≠ 0} := by
  ext point
  constructor
  · rintro ⟨argument, rfl⟩
    exact (polarDiskPoint (argument.1, argument.2.1)).property
  · intro nonzero
    let polar := polarDiskInverse ⟨point.1, nonzero⟩
    refine ⟨(polar.1, polar.2, point.2), ?_⟩
    apply Prod.ext
    · exact congrArg Subtype.val (polarDiskInverse_right ⟨point.1, nonzero⟩)
    · rfl

def referenceTorus (radius : Ioc (0 : ℝ) 1) (angles : Torus) : Reference :=
  referenceFoliation (radius, angles)

theorem referenceTorus_isEmbedding (radius : Ioc (0 : ℝ) 1) : Topology.IsEmbedding (referenceTorus radius) := by
  have insert : Topology.IsEmbedding (fun angles : Torus => (radius, angles)) := by
    exact (show Function.LeftInverse Prod.snd (fun angles : Torus => (radius, angles)) from fun _ => rfl).isEmbedding
      continuous_snd (continuous_const.prodMk continuous_id)
  exact referenceFoliation_isEmbedding.comp insert

theorem referenceTorus_norm (radius : Ioc (0 : ℝ) 1) (angles : Torus) :
    ‖(referenceTorus radius angles).1.val‖ = radius.val := polarDiskValue_norm (radius, angles.1)

theorem referenceTorus_range (radius : Ioc (0 : ℝ) 1) :
    range (referenceTorus radius) = {point : Reference | ‖point.1.val‖ = radius.val} := by
  ext point
  constructor
  · rintro ⟨angles, rfl⟩
    exact referenceTorus_norm radius angles
  · intro normSame
    have nonzero : point.1.val ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [normSame]
      exact radius.property.1.ne'
    let polar := polarDiskInverse ⟨point.1, nonzero⟩
    have radiusSame : polar.1 = radius := Subtype.ext normSame
    refine ⟨(polar.2, point.2), ?_⟩
    change referenceFoliation (radius, polar.2, point.2) = point
    rw [← radiusSame]
    apply Prod.ext
    · exact congrArg Subtype.val (polarDiskInverse_right ⟨point.1, nonzero⟩)
    · rfl

end Grad.PhysicalGeometry
