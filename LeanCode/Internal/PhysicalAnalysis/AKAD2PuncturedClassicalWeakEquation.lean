import AKAD1ClassicalCompactDivergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace Grad.PhysicalAxisEquation
open Grad.PDEBootstrap Grad.RepresentedKernel.SpatialProduct Grad.ClosedJets

/-- Removing the axis point does not change the actual Cartesian volume measure. -/
theorem puncturedDisk_restrict_measure :
    volume.restrict (openUnitDisk \ {(0 : Spatial)}) = volume.restrict openUnitDisk := by
  apply Measure.restrict_congr_set
  have away : ∀ᵐ point : Spatial ∂volume, point ≠ 0 := by simp [ae_iff]
  filter_upwards [away] with point nonzero
  apply propext
  change (point ∈ openUnitDisk ∧ point ≠ 0) ↔ point ∈ openUnitDisk
  exact ⟨fun inside => inside.1,fun inside => ⟨inside,nonzero⟩⟩

/-- A classical equation on the punctured disk yields the exact punctured
weak identity in full Cartesian disk volume, without defining a derivative at zero. -/
theorem punctured_classical_divergence_weak {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (flux : Fin 2 → Spatial → E) (source : Spatial → E)
    (smooth : ∀ index, ContDiffOn ℝ ∞ (flux index) (openUnitDisk \ {(0 : Spatial)}))
    (equation : ∀ point ∈ openUnitDisk \ {(0 : Spatial)}, source point =
      ∑ index : Fin 2, directionDerivative index (flux index) point)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) (supported : tsupport test ⊆ openUnitDisk)
    (away : (0 : Spatial) ∉ tsupport test) :
    (∫ point in openUnitDisk, test point • source point) =
      -(∑ index : Fin 2, ∫ point in openUnitDisk,
        (fderiv ℝ test point (spatialDirection index)) • flux index point) := by
  have openDomain : IsOpen (openUnitDisk \ {(0 : Spatial)}) :=
    openUnitDisk_isOpen.sdiff isClosed_singleton
  have puncturedSupport : tsupport test ⊆ openUnitDisk \ {(0 : Spatial)} := by
    intro point member
    refine ⟨supported member,?_⟩
    simpa only [mem_singleton_iff] using (show point ≠ 0 from fun zero => away (zero ▸ member))
  have result := classical_divergence_compact_test _ openDomain flux source smooth equation
    test testSmooth compact puncturedSupport
  simpa only [puncturedDisk_restrict_measure] using result

end Grad.PhysicalAxisEquation
