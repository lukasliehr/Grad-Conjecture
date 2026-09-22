import AKBV9SameNativeWeightedCells

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators Topology
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap
open Grad.WeightedJets Grad.CartesianStartup Grad.ActualOriginalSourceMoments Grad.RawSourceFaithfulness

/-- The recovered smooth periodic weighted jet has the SAME full integer-cell representative. The input may be the actual scaled and localized analytic field. -/
theorem allDiagonalGraphs_sameWeightedClosedJet {dimension : ℕ} (parameters : PhaseParameters)
    (field : StartupL2 dimension)
    (jets : ∀ grade, GraphGrade dimension grade grade openUnitDisk)
    (sameBase : ∀ grade, base dimension grade openUnitDisk (fun _ => grade) (jets grade) = field) :
    ∃ weighted : DiskCellClosedJet dimension,
      ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        field point cell = closedDiskLift (diskCellFourierCoefficientJet weighted cell).value point := by
  obtain ⟨core,same,_⟩ := allDiagonalGraphs_sameOriginalCore parameters field jets sameBase
  refine ⟨weightedSmoothEquiv parameters core,?_⟩
  have coordinate (cell : ℤ) :
      closedContinuousToDiskL2 (diskCellFourierCoefficientJet (weightedSmoothEquiv parameters core) cell).value =
        fieldCellProjection dimension openUnitDisk cell field := by
    rw [diskCellFourierCoefficientJet_weightedSmoothEquiv,← zeroCell_core,
      originalSourceMoments_zeroCell,same]
  have each (cell : ℤ) : ∀ᵐ point ∂volume.restrict openUnitDisk,
      field point cell = closedDiskLift (diskCellFourierCoefficientJet (weightedSmoothEquiv parameters core) cell).value point := by
    have closed := closedContinuousToDiskL2_ae (diskCellFourierCoefficientJet (weightedSmoothEquiv parameters core) cell).value
    rw [coordinate cell] at closed
    filter_upwards [closed,fieldCellProjection_ae dimension openUnitDisk field] with point actual projected
    exact (projected cell).symm.trans actual
  exact ae_all_iff.mpr each

/-- Equality of the actual continuous cell representatives is recovered on every open punctured region, rather than merely almost everywhere. -/
theorem sameWeightedClosedJet_pointwise {dimension : ℕ}
    (field : StartupL2 dimension) (weighted : DiskCellClosedJet dimension)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      field point cell = closedDiskLift (diskCellFourierCoefficientJet weighted cell).value point)
    (domain : Set Spatial) (openDomain : IsOpen domain) (included : domain ⊆ openUnitDisk)
    (raw : ℤ → Spatial → ComplexEuclidean dimension)
    (continuousRaw : ∀ cell, ContinuousOn (raw cell) domain)
    (sameRaw : ∀ᵐ point ∂volume.restrict domain, ∀ cell : ℤ, field point cell = raw cell point)
    (cell : ℤ) :
    EqOn (closedDiskLift (diskCellFourierCoefficientJet weighted cell).value) (raw cell) domain := by
  apply MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := volume) _ openDomain
    ((diskCellFourierCoefficientJet weighted cell).smoothInterior.continuousOn.mono included)
    (continuousRaw cell)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset included same,sameRaw] with point actual literal
  exact (actual cell).symm.trans (literal cell)

end Grad.CartesianCoreRecovery
