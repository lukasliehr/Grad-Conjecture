import AKDL1ClosedSmoothExtension

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace Grad.PhysicalAmbient
open Grad.MainTarget Grad.PhysicalFamily.SampledSmoothFamily
open Grad.MainAssembly.PhysicalNormalHessian Grad.PhysicalFamily.SampledGlobalEmbedding

local instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩

instance referenceNonempty : Nonempty Reference := ⟨(⟨0, by simp⟩, 0)⟩

/-- The real angular cover of the exact closed reference cylinder. -/
def referenceCover (argument : ClosedDisk × ℝ) : Reference :=
  (argument.1, (argument.2 : CellCircle))

def referenceCoverPoint (argument : ClosedDisk × ℝ) : Vec :=
  coordinateDirection argument.1.val argument.2

theorem referenceCoverPoint_continuous : Continuous referenceCoverPoint := by
  have packingSmooth : ContDiff ℝ ∞ (fun argument : Plane × ℝ =>
      coordinateDirection argument.1 argument.2) := by
    rw [contDiff_piLp]
    intro coordinate
    fin_cases coordinate <;> simp [coordinateDirection, vector] <;> fun_prop
  exact packingSmooth.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem referenceCoverPoint_mem (argument : ClosedDisk × ℝ) :
    referenceCoverPoint argument ∈ cylinder := by
  change ‖planarPart (coordinateDirection argument.1.val argument.2)‖ ≤ 1
  rw [planarPart_coordinateDirection]
  exact argument.1.property

theorem referenceCover_quotientPoint (argument : ClosedDisk × ℝ) :
    quotientPoint (referenceCoverPoint argument) (referenceCoverPoint_mem argument) =
      referenceCover argument := by
  apply Prod.ext
  · apply Subtype.ext
    exact planarPart_coordinateDirection _ _
  · simp [referenceCoverPoint, referenceCover, quotientPoint, coordinateDirection, vector]

theorem referenceCover_isOpenMap : IsOpenMap referenceCover := by
  have idOpen : IsOpenMap (id : ClosedDisk → ClosedDisk) := by
    intro set setOpen
    simpa using setOpen
  exact idOpen.prodMap QuotientAddGroup.isOpenMap_coe

theorem referenceCover_surjective : Function.Surjective referenceCover := by
  intro point
  let representative := (AddCircle.equivIco (2 * Real.pi) 0 point.2).val
  refine ⟨(point.1, representative), ?_⟩
  apply Prod.ext
  · rfl
  · exact (AddCircle.equivIco (2 * Real.pi) 0).symm_apply_apply point.2

theorem reference_isCompact : IsCompact (univ : Set Reference) := by
  have compactDisk : IsCompact {point : Plane | ‖point‖ ≤ 1} := by
    simpa [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : Plane) 1
  let : CompactSpace ClosedDisk := isCompact_iff_compactSpace.mp compactDisk
  exact isCompact_univ

/-- Reconstruction using the inverse of the original embedded reference map. -/
def canonicalAmbientField {Target : Type*} (position : Reference → Vec)
    (field : Reference → Target) : Vec → Target :=
  fun point => field (Function.invFun position point)

theorem canonicalAmbientField_apply {Target : Type*}
    (position : Reference → Vec) (field : Reference → Target)
    (injective : Function.Injective position) (point : Reference) :
    canonicalAmbientField position field (position point) = field point := by
  rw [canonicalAmbientField, Function.leftInverse_invFun injective point]

end Grad.PhysicalAmbient
