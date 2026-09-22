import AOC4ActualFiniteOuterConsumer
import CDO2OrdinaryDiskConsumer
import APR5ActualInteriorH2

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace Grad.ActualFiniteGlobal
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.ActualInverseInduction Grad.InteriorLocalization
open Grad.ActualOuterCollar Grad.ClosedDiskRegularity Grad.OrdinaryDiskCalculus
attribute [local instance] unitNormedSpace

theorem diskSelectedModes_core (modes : Finset ℤ) (core : ClosedJet 1) :
    diskSelectedModes modes (closedL2Core core) = closedL2Core (selectedAngularJet modes core) := by
  rw [diskSelectedModes_apply, selectedAngularJet_eq, map_sum]
  exact Finset.sum_congr rfl (fun mode _ => diskMode_core mode core)

theorem selectedSource_core (modes : Finset ℤ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    (highL2SelectedModes modes source).val = closedL2Core (selectedAngularJet modes core) :=
  (highL2SelectedModes_val modes source).trans
    ((congrArg (diskSelectedModes modes) same).trans (diskSelectedModes_core modes core))

def selectedForcing (grade : ℕ) (modes : Finset ℤ) (core : ClosedJet 1) : unitDiskSobolev grade :=
  unitDiskCoreInto grade (selectedAngularJet modes core)

theorem selectedForcing_bulk (grade : ℕ) (modes : Finset ℤ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    unitDiskBulk grade (selectedForcing grade modes core) = (highL2SelectedModes modes source).val :=
  (unitDiskBulk_core grade (selectedAngularJet modes core)).trans (selectedSource_core modes source core same).symm

/-- The actual outer representative exists on every ordinary Sobolev grade,
from the proved closed-disk smooth finite angular field. -/
def finiteOuterOrdinary (grade : ℕ) (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core) : unitDiskSobolev grade :=
  withinOrdinaryDisk grade (finiteOuterField modes parameter source)
    (finiteOuterField_smooth modes parameter source core same)

theorem finiteOuterOrdinary_bulk (grade : ℕ) (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    unitDiskBulk grade (finiteOuterOrdinary grade modes parameter source core same) =
      diskScalar outerCutoffScalar outerCutoffScalar_smooth
        (highDiskBulk (highRobinWeakInverse parameter (highL2SelectedModes modes source))) :=
  withinOrdinaryDisk_same grade (finiteOuterField modes parameter source)
    (finiteOuterField_smooth modes parameter source core same) _ (finiteOuterField_bulk_ae modes parameter source)

end Grad.ActualFiniteGlobal
