import AOG2ActualGlobalInduction

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators

namespace Grad.ActualFiniteGlobal
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.ActualInverseInduction Grad.InteriorLocalization
open Grad.ActualOuterCollar Grad.ClosedDiskRegularity Grad.OrdinaryDiskCalculus Grad.PDEBootstrap
attribute [local instance] unitNormedSpace

/-- An actual representative in each ordinary Cartesian grade, chosen from
the completed global induction. Every choice has the same literal L2 bulk. -/
def finiteGlobalRepresentative (parameters : PhaseParameters) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (grade : ℕ) : unitDiskSobolev grade :=
  (finiteGlobal_everyGrade parameters modes parameter source core same grade).choose

theorem finiteGlobalRepresentative_bulk (parameters : PhaseParameters) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (grade : ℕ) :
    unitDiskBulk grade (finiteGlobalRepresentative parameters modes parameter source core same grade) =
      highDiskBulk (highRobinWeakInverse parameter (highL2SelectedModes modes source)) :=
  (finiteGlobal_everyGrade parameters modes parameter source core same grade).choose_spec

theorem finiteGlobalRepresentative_equation (parameters : PhaseParameters) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (grade : ℕ) :
    HasDiskWeakLaplacian
      (unitDiskBulk grade (finiteGlobalRepresentative parameters modes parameter source core same grade))
      (weakLaplacianValue parameter (highL2SelectedModes modes source)) :=
  (congrArg (fun field => HasDiskWeakLaplacian field
    (weakLaplacianValue parameter (highL2SelectedModes modes source)))
      (finiteGlobalRepresentative_bulk parameters modes parameter source core same grade)).mpr
    (weakInverse_distribution parameter (highL2SelectedModes modes source))

/-- The exact finite angular global regularity consumer. The source is the
selected ORIGINAL smooth source and every ordinary grade represents the
same constructed Robin inverse with its unchanged weak equation. There is
no uniform bound in the finite set and no all-mode limit assertion. -/
theorem actualFiniteAngularGlobalRegularity (parameters : PhaseParameters) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    ∃ representatives : (grade : ℕ) → unitDiskSobolev grade,
      ∀ grade,
        unitDiskBulk grade (representatives grade) =
          highDiskBulk (highRobinWeakInverse parameter (highL2SelectedModes modes source)) ∧
        HasDiskWeakLaplacian (unitDiskBulk grade (representatives grade))
          (weakLaplacianValue parameter (highL2SelectedModes modes source)) :=
  ⟨finiteGlobalRepresentative parameters modes parameter source core same,
    fun grade => ⟨finiteGlobalRepresentative_bulk parameters modes parameter source core same grade,
      finiteGlobalRepresentative_equation parameters modes parameter source core same grade⟩⟩

/-- If the original smooth source already has the given finite angular
support, the representatives are of its original inverse without selection. -/
theorem actualFinitelySupportedGlobalRegularity (parameters : PhaseParameters) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (supported : highL2SelectedModes modes source = source) :
    ∃ representatives : (grade : ℕ) → unitDiskSobolev grade,
      ∀ grade, unitDiskBulk grade (representatives grade) = highDiskBulk (highRobinWeakInverse parameter source) ∧
        HasDiskWeakLaplacian (unitDiskBulk grade (representatives grade)) (weakLaplacianValue parameter source) := by
  have result := actualFiniteAngularGlobalRegularity parameters modes parameter source core same
  exact (congrArg (fun data : highDiskL2 => ∃ representatives : (grade : ℕ) → unitDiskSobolev grade,
    ∀ grade, unitDiskBulk grade (representatives grade) = highDiskBulk (highRobinWeakInverse parameter data) ∧
      HasDiskWeakLaplacian (unitDiskBulk grade (representatives grade)) (weakLaplacianValue parameter data)) supported).mp result

end Grad.ActualFiniteGlobal
