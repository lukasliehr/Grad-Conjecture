import ABF2SameBulkSmoothRealization

noncomputable section
namespace Grad.OrdinaryDiskFaithfulness
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CompatibleCompletion
open Grad.OrdinaryDiskReconstruction Grad.OrdinaryDiskForward Grad.OrdinaryDiskCalculus
open Grad.ActualFiniteGlobal
attribute [local instance] unitNormedSpace

/-- One genuine smooth closed-disk jet of the same finite-selected ANH inverse. -/
def finiteInverseClosedJet (parameters : PhaseParameters) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) : ClosedJet 1 :=
  sameBulkClosedJet parameters (finiteGlobalRepresentative parameters modes parameter source core same)
    (highDiskBulk (highRobinWeakInverse parameter (highL2SelectedModes modes source)))
    (finiteGlobalRepresentative_bulk parameters modes parameter source core same)

theorem finiteInverseClosedJet_grade (parameters : PhaseParameters) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (grade : ℕ) :
    unitDiskCoreInto grade (finiteInverseClosedJet parameters modes parameter source core same) =
      finiteGlobalRepresentative parameters modes parameter source core same grade :=
  sameBulkClosedJet_core parameters _ _ _ grade

theorem finiteInverseClosedJet_bulk (parameters : PhaseParameters) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    closedL2Core (finiteInverseClosedJet parameters modes parameter source core same) =
      highDiskBulk (highRobinWeakInverse parameter (highL2SelectedModes modes source)) :=
  sameBulkClosedJet_bulk parameters _ _ _

/-- The closed jet recovers the complete actual H1 graph, hence the same
weak Robin form and boundary trace, not merely the same value function. -/
theorem finiteInverseClosedJet_H1 (parameters : PhaseParameters) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    diskCoreInto (finiteInverseClosedJet parameters modes parameter source core same) =
      (highRobinWeakInverse parameter (highL2SelectedModes modes source)).val := by
  apply diskBulk_injective
  exact (Grad.CircularHighWeak.diskBulk_core _).trans
    (finiteInverseClosedJet_bulk parameters modes parameter source core same)

/-- Actual finite angular smooth reconstruction: one closed jet agrees with
the constructed ANH H1 inverse and every original ordinary Sobolev grade. -/
theorem actualFiniteSmoothInverse (parameters : PhaseParameters) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    ∃ solution : ClosedJet 1,
      diskCoreInto solution = (highRobinWeakInverse parameter (highL2SelectedModes modes source)).val ∧
      ∀ grade, unitDiskCoreInto grade solution =
        finiteGlobalRepresentative parameters modes parameter source core same grade :=
  ⟨finiteInverseClosedJet parameters modes parameter source core same,
    finiteInverseClosedJet_H1 parameters modes parameter source core same,
    finiteInverseClosedJet_grade parameters modes parameter source core same⟩

end Grad.OrdinaryDiskFaithfulness
