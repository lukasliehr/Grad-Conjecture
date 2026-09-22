import AKCF3OrdinaryAllOrderGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators
namespace Grad.NativePuncturedGraph
open Grad.ClosedJets Grad.CartesianState Grad.CartesianCoreRecovery Grad.SourceCollarDivision
open Grad.ActualSmoothPhysicalField Grad.Constraints Grad.DiskExtension.Operator Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients Grad.BoundaryTrace
open Grad.PDEBootstrap Grad.GenericCarriers Grad.CartesianStartup Grad.WeightedJets

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower<1) (scale : ℝ) (cutoff : SpatialPlane→ℝ)
    (smooth : ContDiff ℝ ∞ cutoff)
    (supported : tsupport cutoff⊆{point | ‖scale • point‖∈Ioo lower 1})

theorem nativeAnnularCutoffJet_cell (point : ClosedDisk) (cell : ℤ) :
    (diskCellFourierCoefficientJet (nativeAnnularCutoffJet curves bounded scale cutoff smooth supported) cell).value point=
      cutoff point.val • (cartesianWeight parameters cell (scale • point.val) •
        angularCoefficient (fun axial => curves.cartesianField bounded (scale • point.val,axial)) cell) := by
  rw [diskCellFourierCoefficientJet_value,diskCellFourierValue_apply,←angularCoefficient_circle]
  simp_rw [nativeAnnularCutoffJet_value]
  rw [angularCoefficient_real_smul]
  by_cases zero : cutoff point.val=0
  · simp only [zero,zero_smul]
  · have inside : ‖scale • point.val‖∈Icc lower 1 :=
      ⟨(supported (subset_closure zero)).1.le,(supported (subset_closure zero)).2.le⟩
    rw [nativeWeightedOuter_cell curves bounded _ inside]

/-- The SAME weighted full native field, localized by an arbitrary smooth
annular cutoff, has every ordered spatial graph and every cell weight. -/
def nativeAnnularCutoffGraph (order weight : ℕ) : GraphGrade dimension order weight openUnitDisk :=
  ordinaryAllOrderGraph (ordinaryFourierCoefficientCore (nativeAnnularCutoffJet curves bounded scale cutoff smooth supported)) order weight

theorem nativeAnnularCutoffGraph_same (order weight : ℕ) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      base dimension order openUnitDisk (fun _ => weight)
        (nativeAnnularCutoffGraph curves bounded scale cutoff smooth supported order weight) point cell=
      cutoff point • (cartesianWeight parameters cell (scale • point) •
        angularCoefficient (fun axial => curves.cartesianField bounded (scale • point,axial)) cell) := by
  filter_upwards [ordinaryAllOrderGraph_same
    (ordinaryFourierCoefficientCore (nativeAnnularCutoffJet curves bounded scale cutoff smooth supported)) order weight,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point same inside
  intro cell
  apply (same cell).trans
  rw [closedDiskLift,dif_pos (openDiskMembershipClosed point inside)]
  exact nativeAnnularCutoffJet_cell curves bounded scale cutoff smooth supported ⟨point,openDiskMembershipClosed point inside⟩ cell

end Grad.NativePuncturedGraph
