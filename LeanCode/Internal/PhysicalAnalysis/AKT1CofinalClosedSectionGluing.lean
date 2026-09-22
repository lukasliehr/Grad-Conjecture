import AKP12FullOriginalFamilyVanishingIncoming
import AKP9OriginalAdmissibleCofinalRadii
import AKB10ExactSameOriginalPhase

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Set Filter
open scoped Topology
namespace Grad.ActualPuncturedFamily
open Grad.AnnularSourceGraph

variable (lower : ℕ → ℝ) (cofinal : Tendsto lower atTop (𝓝 0))
include cofinal

/-- A positive radius has a collar strictly below it, leaving a genuine
neighborhood on which the same local field can be used. -/
theorem exists_strict_inner_collar (radius : ℝ) (positive : 0 < radius) :
    ∃ index, lower index < radius :=
  ((cofinal.eventually (gt_mem_nhds positive))).exists

def selectedInnerCollar (radius : ℝ) (positive : 0 < radius) : ℕ :=
  Nat.find (exists_strict_inner_collar lower cofinal radius positive)

theorem selectedInnerCollar_lt (radius : ℝ) (positive : 0 < radius) :
    lower (selectedInnerCollar lower cofinal radius positive) < radius :=
  Nat.find_spec (exists_strict_inner_collar lower cofinal radius positive)

variable {E : Type*} [TopologicalSpace E] [Zero E]
    (sections : ∀ index, C(Icc (lower index) (1 : ℝ), E))

/-- One field on the punctured closed disk radius interval, selected from
actual compatible closed-collar sections. -/
def gluedClosedSections (radius : ℝ) : E :=
  if inside : radius ∈ Ioc (0 : ℝ) 1 then
    sections (selectedInnerCollar lower cofinal radius inside.1)
      ⟨radius, (selectedInnerCollar_lt lower cofinal radius inside.1).le, inside.2⟩
  else 0

variable (positive : ∀ index, 0 < lower index)
    (compatible : ∀ first second (radius : ℝ) (one : radius ∈ Icc (lower first) 1)
      (two : radius ∈ Icc (lower second) 1), sections first ⟨radius,one⟩ = sections second ⟨radius,two⟩)

include positive compatible

/-- Every local section is recovered pointwise, including both its endpoints. -/
theorem gluedClosedSections_same (index : ℕ) (radius : ℝ) (inside : radius ∈ Icc (lower index) 1) :
    gluedClosedSections lower cofinal sections radius = sections index ⟨radius,inside⟩ := by
  have punctured : radius ∈ Ioc (0 : ℝ) 1 := ⟨(positive index).trans_le inside.1,inside.2⟩
  rw [gluedClosedSections,dif_pos punctured]
  exact compatible _ index radius _ inside

/-- Compatibility glues actual continuous sections without choosing new
pointwise representatives on overlaps. -/
theorem gluedClosedSections_continuous (bounded : ∀ index, lower index ≤ 1) :
    ContinuousOn (gluedClosedSections lower cofinal sections) (Ioc (0 : ℝ) 1) := by
  intro radius inside
  let index := selectedInnerCollar lower cofinal radius inside.1
  have below : lower index < radius := selectedInnerCollar_lt lower cofinal radius inside.1
  let localCurve := fun point => sections index (radialClamp (lower index) (bounded index) point)
  have continuous : Continuous localCurve := (sections index).continuous.comp (radialClamp_continuous (lower index) (bounded index))
  have equal : gluedClosedSections lower cofinal sections =ᶠ[𝓝[Ioc (0 : ℝ) 1] radius] localCurve := by
    filter_upwards [self_mem_nhdsWithin, (lt_mem_nhds below).filter_mono nhdsWithin_le_nhds] with point member greater
    have localInside : point ∈ Icc (lower index) 1 := ⟨greater.le,member.2⟩
    rw [gluedClosedSections_same lower cofinal sections positive compatible index point localInside]
    change sections index ⟨point,localInside⟩ = sections index (radialClamp (lower index) (bounded index) point)
    rw [radialClamp_eq (lower index) (bounded index) point localInside]
  have exactAt : gluedClosedSections lower cofinal sections radius = localCurve radius := by
    have localInside : radius ∈ Icc (lower index) 1 := ⟨below.le,inside.2⟩
    rw [gluedClosedSections_same lower cofinal sections positive compatible index radius localInside]
    change sections index ⟨radius,localInside⟩ = sections index (radialClamp (lower index) (bounded index) radius)
    rw [radialClamp_eq (lower index) (bounded index) radius localInside]
  exact continuous.continuousAt.continuousWithinAt.congr_of_eventuallyEq equal exactAt

end Grad.ActualPuncturedFamily
