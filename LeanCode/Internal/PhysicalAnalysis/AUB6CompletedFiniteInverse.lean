import AUB4ActualFiniteUniformGain
import AUB5FiniteProjectionAlgebra
import AST7ActualSourceConsumer

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter
open scoped Topology
namespace Grad.ActualUniformGlobal
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.OrdinaryDiskFaithfulness Grad.OrdinaryDiskCalculus Grad.AngularSobolevTruncation
attribute [local instance] unitNormedSpace

def finiteInverseConstant (grade : ℕ) (ceiling : ℝ) : ℝ :=
  (finiteSmoothInverse_uniform_gain grade ceiling).choose

theorem finiteInverseConstant_nonnegative (grade : ℕ) (ceiling : ℝ) :
    0 ≤ finiteInverseConstant grade ceiling := (finiteSmoothInverse_uniform_gain grade ceiling).choose_spec.1

theorem finiteInverseConstant_core_bound (grade : ℕ) (ceiling : ℝ) (parameters : PhaseParameters)
    (parameter : ℝ) (bounded : |parameter| ≤ ceiling) (modes : Finset ℤ) (core : ClosedJet 1) :
    ‖unitDiskCoreInto (grade + 2) (finiteSmoothInverseLinear parameters modes parameter core)‖ ≤
      finiteInverseConstant grade ceiling * ‖unitDiskCoreInto grade core‖ :=
  (finiteSmoothInverse_uniform_gain grade ceiling).choose_spec.2 parameters parameter bounded modes core

theorem finiteCompletedInverse_exists (grade : ℕ) (parameters : PhaseParameters)
    (parameter : ℝ) (modes : Finset ℤ) :
    ∃ completed : unitDiskSobolev grade →L[ℂ] unitDiskSobolev (grade + 2),
      (∀ core, completed (unitDiskCoreInto grade core) =
        unitDiskCoreInto (grade + 2) (finiteSmoothInverseLinear parameters modes parameter core)) ∧
      (∀ source, ‖completed source‖ ≤ finiteInverseConstant grade |parameter| * ‖source‖) := by
  apply unitCore_extension grade (grade + 2) (finiteSmoothInverseLinear parameters modes parameter)
    (finiteInverseConstant grade |parameter|) (finiteInverseConstant_nonnegative grade |parameter|)
  intro core
  simpa only [unitDiskCore_norm] using
    finiteInverseConstant_core_bound grade |parameter| parameters parameter le_rfl modes core

def finiteCompletedInverse (grade : ℕ) (parameters : PhaseParameters) (parameter : ℝ) (modes : Finset ℤ) :
    unitDiskSobolev grade →L[ℂ] unitDiskSobolev (grade + 2) :=
  (finiteCompletedInverse_exists grade parameters parameter modes).choose

theorem finiteCompletedInverse_core (grade : ℕ) (parameters : PhaseParameters)
    (parameter : ℝ) (modes : Finset ℤ) (core : ClosedJet 1) :
    finiteCompletedInverse grade parameters parameter modes (unitDiskCoreInto grade core) =
      unitDiskCoreInto (grade + 2) (finiteSmoothInverseLinear parameters modes parameter core) :=
  (finiteCompletedInverse_exists grade parameters parameter modes).choose_spec.1 core

theorem finiteCompletedInverse_uniform (grade : ℕ) (ceiling : ℝ) (parameters : PhaseParameters)
    (parameter : ℝ) (bounded : |parameter| ≤ ceiling) (modes : Finset ℤ) (source : unitDiskSobolev grade) :
    ‖finiteCompletedInverse grade parameters parameter modes source‖ ≤
      finiteInverseConstant grade ceiling * ‖source‖ := by
  apply isClosed_property (unitDiskCoreInto_denseRange grade)
    (isClosed_le (finiteCompletedInverse grade parameters parameter modes).continuous.norm
      (continuous_const.mul continuous_norm)) _ source
  intro core
  change ‖finiteCompletedInverse grade parameters parameter modes (unitDiskCoreInto grade core)‖ ≤
    finiteInverseConstant grade ceiling * ‖unitDiskCoreInto grade core‖
  rw [finiteCompletedInverse_core]
  exact finiteInverseConstant_core_bound grade ceiling parameters parameter bounded modes core

/-- Exact literal bulk of the finite completed inverse, including all
nonsmooth ordinary Hs sources, with only the five low modes projected out. -/
theorem finiteCompletedInverse_bulk (grade : ℕ) (parameters : PhaseParameters)
    (parameter : ℝ) (modes : Finset ℤ) (source : unitDiskSobolev grade) :
    unitDiskBulk (grade + 2) (finiteCompletedInverse grade parameters parameter modes source) =
      highDiskBulk (highRobinWeakInverse parameter
        (highL2SelectedModes modes (highL2ProjectionInto (unitDiskBulk grade source)))) := by
  apply isClosed_property (unitDiskCoreInto_denseRange grade)
    (isClosed_eq ((unitDiskBulk (grade + 2)).continuous.comp
      (finiteCompletedInverse grade parameters parameter modes).continuous)
      (highDiskBulk.continuous.comp ((highRobinWeakInverse parameter).continuous.comp
        ((highL2SelectedModes modes).continuous.comp (highL2ProjectionInto.continuous.comp
          (unitDiskBulk grade).continuous))))) _ source
  intro core
  change unitDiskBulk (grade + 2)
    (finiteCompletedInverse grade parameters parameter modes (unitDiskCoreInto grade core)) = _
  calc
    _ = unitDiskBulk (grade + 2)
        (unitDiskCoreInto (grade + 2) (finiteSmoothInverseLinear parameters modes parameter core)) :=
      congrArg (unitDiskBulk (grade + 2)) (finiteCompletedInverse_core grade parameters parameter modes core)
    _ = closedL2Core (finiteSmoothInverseLinear parameters modes parameter core) :=
      unitDiskBulk_core (grade + 2) _
    _ = highDiskBulk (highRobinWeakInverse parameter
        (highL2SelectedModes modes (highL2ProjectionInto (closedL2Core core)))) :=
      finiteSmoothInverse_bulk parameters modes parameter core
    _ = _ := congrArg (fun bulk => highDiskBulk (highRobinWeakInverse parameter
      (highL2SelectedModes modes (highL2ProjectionInto bulk)))) (unitDiskBulk_core grade core).symm

end Grad.ActualUniformGlobal
