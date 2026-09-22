import AKBV15ActualNativeOuterGluing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter
open scoped ContDiff Topology
namespace Grad.NativePuncturedGraph
open Grad.ClosedJets Grad.CartesianState Grad.CartesianCoreRecovery Grad.SourceCollarDivision
open Grad.ActualSmoothPhysicalField Grad.Constraints Grad.DiskExtension.Operator

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower<1) (scale : ℝ) (cutoff : SpatialPlane→ℝ)
    (smooth : ContDiff ℝ ∞ cutoff)
    (supported : tsupport cutoff⊆{point | ‖scale • point‖∈Ioo lower 1})

def nativeAnnularCutoffField (point : SpatialCell) : ComplexEuclidean dimension :=
  cutoff (planarPart point) • nativeWeightedOuter curves bounded
    (assembleSpatialCell (scale • planarPart point) (point 2))

include smooth supported in
theorem nativeAnnularCutoffField_smooth : ContDiff ℝ ∞ (nativeAnnularCutoffField curves bounded scale cutoff) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  have planarSmooth : ContDiff ℝ ∞ planarPart := planarPartCLM.contDiff
  by_cases inside : planarPart point∈tsupport cutoff
  · have domainOpen : IsOpen {query : SpatialCell | ‖planarPart query‖∈Ioo lower 1} :=
      isOpen_Ioo.preimage planarPartCLM.continuous.norm
    have within : ContDiffOn ℝ ∞ (nativeWeightedOuter curves bounded) {query : SpatialCell | ‖planarPart query‖∈Ioo lower 1} := (nativeWeightedOuter_smooth curves bounded).mono
      (fun query member => ⟨member.1.le,member.2.le⟩)
    have atField := within.contDiffAt (domainOpen.mem_nhds (by
      change ‖planarPart (assembleSpatialCell (scale • planarPart point) (point 2))‖∈Ioo lower 1
      rw [planarPart_assembleSpatialCell]
      exact supported inside))
    have mapping : ContDiff ℝ ∞ (fun query : SpatialCell => assembleSpatialCell (scale • planarPart query) (query 2)) :=
      assembleSpatialCellCLM.contDiff.comp (((contDiff_const : ContDiff ℝ ∞ (fun _ : SpatialCell => scale)).smul planarSmooth).prodMk cellCoordinateCLM.contDiff)
    have composite : ContDiffAt ℝ ∞ (fun query : SpatialCell => nativeWeightedOuter curves bounded
        (assembleSpatialCell (scale • planarPart query) (query 2))) point :=
      ContDiffAt.comp (f := fun query : SpatialCell => assembleSpatialCell (scale • planarPart query) (query 2))
        (g := nativeWeightedOuter curves bounded) point atField mapping.contDiffAt
    have result := ((smooth.comp planarSmooth).contDiffAt (x := point)).smul composite
    exact result
  · have neighborhood : ∀ᶠ query in 𝓝 point, planarPart query∉tsupport cutoff :=
      planarPartCLM.continuous.continuousAt.preimage_mem_nhds ((isClosed_tsupport cutoff).isOpen_compl.mem_nhds inside)
    apply (contDiffAt_const (c := (0 : ComplexEuclidean dimension))).congr_of_eventuallyEq
    filter_upwards [neighborhood] with query outside
    have zero : cutoff (planarPart query)=0 := by
      by_contra nonzero
      exact outside (subset_closure nonzero)
    simp only [nativeAnnularCutoffField,zero,zero_smul]

theorem nativeAnnularCutoffField_periodic (point : SpatialPlane) :
    Function.Periodic (fun axial => nativeAnnularCutoffField curves bounded scale cutoff (assembleSpatialCell point axial)) (2*Real.pi) := by
  intro axial
  simp only [nativeAnnularCutoffField,planarPart_assembleSpatialCell]
  exact congrArg (fun value => cutoff point • value) (nativeWeightedOuter_periodic curves bounded (scale • point) axial)

/-- The actual weighted native field times any smooth cutoff inside a strict
annulus determines a genuine closed cylinder jet, at the SAME spatial scale. -/
def nativeAnnularCutoffJet : DiskCellClosedJet dimension :=
  periodicClosedCylinderJet (nativeAnnularCutoffField curves bounded scale cutoff)
    (nativeAnnularCutoffField_smooth curves bounded scale cutoff smooth supported).contDiffOn
    (nativeAnnularCutoffField_periodic curves bounded scale cutoff)

theorem nativeAnnularCutoffJet_value (point : ClosedDisk) (axial : ℝ) :
    (nativeAnnularCutoffJet curves bounded scale cutoff smooth supported).value (point,(axial : CellCircle))=
      cutoff point.val • nativeWeightedOuter curves bounded (assembleSpatialCell (scale • point.val) axial) :=
by
  have actual := periodicClosedCylinderJet_actual (nativeAnnularCutoffField curves bounded scale cutoff)
    (nativeAnnularCutoffField_smooth curves bounded scale cutoff smooth supported).contDiffOn
    (nativeAnnularCutoffField_periodic curves bounded scale cutoff) point axial
  change (nativeAnnularCutoffJet curves bounded scale cutoff smooth supported).value (point,(axial : CellCircle))=
    cutoff (planarPart (assembleSpatialCell point.val axial)) • nativeWeightedOuter curves bounded
      (assembleSpatialCell (scale • planarPart (assembleSpatialCell point.val axial)) (assembleSpatialCell point.val axial 2)) at actual
  rw [planarPart_assembleSpatialCell] at actual
  simpa only [show assembleSpatialCell point.val axial 2=axial by simp [assembleSpatialCell]] using actual

end Grad.NativePuncturedGraph
