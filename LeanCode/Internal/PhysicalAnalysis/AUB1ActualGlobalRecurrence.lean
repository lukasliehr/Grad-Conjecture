import ABF3ActualFiniteSmoothInverse

noncomputable section
set_option maxHeartbeats 800000
namespace Grad.ActualUniformGlobal
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.ActualFiniteGlobal
open Grad.OrdinaryDiskFaithfulness Grad.OrdinaryDiskCalculus Grad.ActualInverseInduction
open Grad.OrdinaryDiskReconstruction Grad.InteriorLocalization Grad.OrdinaryInteriorBootstrap
attribute [local instance] unitNormedSpace

/-- The qualitative finite family has the actual uniform H1 inverse bound. -/
theorem finiteGlobal_H1_bound (parameters : PhaseParameters) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1)
    (same : source.val = closedL2Core core) :
    ‖finiteGlobalRepresentative parameters modes parameter source core same 1‖ ≤ 2 * ‖source‖ := by
  rw [← finiteInverseClosedJet_grade parameters modes parameter source core same 1]
  have identity : ‖unitDiskCoreInto 1 (finiteInverseClosedJet parameters modes parameter source core same)‖ =
      ‖diskCoreInto (finiteInverseClosedJet parameters modes parameter source core same)‖ := rfl
  rw [identity, finiteInverseClosedJet_H1]
  exact (weakSolution_bound parameter (highL2SelectedModes modes source)).trans
    (mul_le_mul_of_nonneg_left (highL2SelectedModes_contract modes source) (by norm_num))

/-- Faithfulness transfers the genuine interior estimate to the already
constructed finite global representative, retaining the literal outer norm. -/
theorem finiteGlobal_H2_bound (parameters : PhaseParameters) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1)
    (same : source.val = closedL2Core core) :
    ‖finiteGlobalRepresentative parameters modes parameter source core same 2‖ ≤
      interiorOrdinaryConstant * (1 + parameter ^ 2) * ‖highL2SelectedModes modes source‖ +
        ‖finiteOuterOrdinary 2 modes parameter source core same‖ := by
  obtain ⟨interior, interiorSame, bound⟩ :=
    actualInteriorOrdinaryH2 parameters parameter (highL2SelectedModes modes source)
  let outer := finiteOuterOrdinary 2 modes parameter source core same
  have literal : unitDiskBulk 2 (interior + outer) =
      highDiskBulk (highRobinWeakInverse parameter (highL2SelectedModes modes source)) :=
    ((unitDiskBulk 2).map_add interior outer).trans
      ((congrArg₂ (fun first second : DiskL2 1 => first + second) interiorSame
        (finiteOuterOrdinary_bulk 2 modes parameter source core same)).trans (actualCutoff_partition _))
  have identity := ordinaryBulk_injective parameters 2
    (literal.trans (finiteGlobalRepresentative_bulk parameters modes parameter source core same 2).symm)
  rw [← identity]
  exact (norm_add_le interior outer).trans (add_le_add bound le_rfl)

theorem finiteGlobal_step_bound (parameters : PhaseParameters) (grade : ℕ) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1)
    (same : source.val = closedL2Core core) :
    ‖finiteGlobalRepresentative parameters modes parameter source core same (grade + 2)‖ ≤
      inverseInteriorStateConstant grade parameter *
        ‖finiteGlobalRepresentative parameters modes parameter source core same (grade + 1)‖ +
      ordinaryInteriorSourceConstant grade * ‖selectedForcing grade modes core‖ +
      ‖finiteOuterOrdinary (grade + 2) modes parameter source core same‖ := by
  obtain ⟨global, literal, _equation, bound⟩ := actualGlobal_inductionStep parameters grade parameter
    (highL2SelectedModes modes source)
    (finiteGlobalRepresentative parameters modes parameter source core same (grade + 1))
    (selectedForcing grade modes core)
    (finiteGlobalRepresentative_bulk parameters modes parameter source core same (grade + 1))
    (selectedForcing_bulk grade modes source core same)
    (finiteOuterOrdinary (grade + 2) modes parameter source core same)
    (finiteOuterOrdinary_bulk (grade + 2) modes parameter source core same)
  have identity := ordinaryBulk_injective parameters (grade + 2)
    (literal.trans (finiteGlobalRepresentative_bulk parameters modes parameter source core same (grade + 2)).symm)
  exact (congrArg norm identity).symm.le.trans bound

theorem finiteGlobal_lower (parameters : PhaseParameters) {low high : ℕ} (ordered : low ≤ high)
    (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1)
    (same : source.val = closedL2Core core) :
    unitLower ordered (finiteGlobalRepresentative parameters modes parameter source core same high) =
      finiteGlobalRepresentative parameters modes parameter source core same low :=
  ordinaryFamily_compatible parameters _ _
    (finiteGlobalRepresentative_bulk parameters modes parameter source core same) low high ordered

end Grad.ActualUniformGlobal
