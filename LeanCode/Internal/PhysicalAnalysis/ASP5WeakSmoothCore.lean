import ASP1AngularPrimitive

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualSmoothPDE
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.GenericCarriers Grad.NonlinearDivision
open Grad.GaugeCoefficients.Physical.RadialLedger

private theorem diskPairing_integrable (vector : PhysicalValue 1)
    (test : Grad.PDEBootstrap.Spatial → ℝ) (membership : MemLp test 2 (volume.restrict openUnitDisk))
    (field : DiskL2 1) :
    Integrable (fun point => test point • inner ℂ vector (field point)) (volume.restrict openUnitDisk) := by
  have integrable := Grad.WeakTesting.pairing_integrable 1 openUnitDisk 0 vector test membership (apDiskInjection 1 field)
  apply integrable.congr
  filter_upwards [apDiskInjection_ae field] with point literal
  rw [literal]
  rfl

/-- Every genuine smooth closed jet has its literal Cartesian Laplacian
as its full distributional Laplacian on the original open disk. -/
theorem closedL2Core_weakLaplacian (core : ClosedJet 1) :
    HasDiskWeakLaplacian (closedL2Core core) (closedL2Core (laplacianJet core)) := by
  intro vector test smooth compact supported
  have first := apClosedJet_weak core (fun _ : Fin 2 => (0 : Fin 2)) 0 vector test smooth compact supported
  have second := apClosedJet_weak core (fun _ : Fin 2 => (1 : Fin 2)) 0 vector test smooth compact supported
  have laplacianBulk : closedL2Core (laplacianJet core) =
      closedContinuousToDiskL2 (closedDerivative core 2 (fun _ => 0)) +
      closedContinuousToDiskL2 (closedDerivative core 2 (fun _ => 1)) := by
    change closedContinuousToDiskL2 (laplacianJet core).value = _
    rw [laplacianJet_value]
    exact closedContinuousToDiskL2_add _ _
  rw [← apDiskPairing_literal vector test smooth compact, laplacianBulk, map_add, first, second]
  norm_num only [neg_one_sq, one_mul]
  rw [apDiskDerivativePairing_literal, apDiskDerivativePairing_literal]
  unfold testLaplacian
  simp only [Pi.add_apply, add_smul]
  exact (integral_add
    (diskPairing_integrable vector _ (Grad.WeakTesting.orderedTestDerivative_memLp openUnitDisk 2 (fun _ => 0) test smooth compact) _)
    (diskPairing_integrable vector _ (Grad.WeakTesting.orderedTestDerivative_memLp openUnitDisk 2 (fun _ => 1) test smooth compact) _)).symm

private theorem apDiskPairing_nonzeroCell (cell : ℤ) (nonzero : cell ≠ 0) (vector : PhysicalValue 1)
    (test : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) (field : DiskL2 1) :
    apDiskPairing 1 cell vector test smooth compact field = 0 := by
  rw [apDiskPairing, ContinuousLinearMap.comp_apply, Grad.WeakTesting.compactPairing_apply]
  apply integral_eq_zero_of_ae
  filter_upwards [apDiskInjection_ae field] with point literal
  rw [literal]
  simp [cellSingle, lp.single_apply, nonzero]

/-- Uniqueness here is the already proved separation by ordinary compact
Cartesian tests; there is no extra regularity or strong-solution premise. -/
theorem diskWeakLaplacian_unique (field first second : DiskL2 1)
    (firstLaw : HasDiskWeakLaplacian field first) (secondLaw : HasDiskWeakLaplacian field second) :
    first = second := by
  apply apDiskPairing_separates
  intro cell vector test smooth compact supported
  by_cases zero : cell = 0
  · subst cell
    rw [apDiskPairing_literal, apDiskPairing_literal,
      firstLaw vector test smooth compact supported, secondLaw vector test smooth compact supported]
  · rw [apDiskPairing_nonzeroCell cell zero, apDiskPairing_nonzeroCell cell zero]

/-- The literal weak inverse Laplacian is identified for any smooth jet
representing its accepted H1 solution, with no source smoothness needed. -/
theorem sameH1_laplacian_bulk (parameter : ℝ) (source : highDiskL2) (solution : ClosedJet 1)
    (same : diskCoreInto solution = (highRobinWeakInverse parameter source).val) :
    closedL2Core (laplacianJet solution) = weakLaplacianValue parameter source := by
  have bulk : closedL2Core solution = highDiskBulk (highRobinWeakInverse parameter source) :=
    (Grad.CircularHighRegularity.diskBulk_core solution).symm.trans (congrArg diskBulk same)
  apply diskWeakLaplacian_unique (closedL2Core solution)
  · exact closedL2Core_weakLaplacian solution
  · rw [bulk]
    exact weakInverse_distribution parameter source

end Grad.ActualSmoothPDE
