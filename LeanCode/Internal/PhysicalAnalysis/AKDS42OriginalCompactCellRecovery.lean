import AKDS41OriginalUnitCurrentRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace Grad.OriginalCoreRealization
open Grad.CartesianState Grad.NonlinearProduct Grad.NonlinearQuotientBounds Grad.CartesianStartup
open Grad.OriginalCartesianTameEstimate Grad.GaugeCoefficients.Physical.RadialLedger

/-- The fixed circle projection retains pure-cell bounds without introducing
an unknown higher norm of its original covariant input. -/
theorem originalCircle_sameCore_cell_bound (parameters : PhaseParameters) :
    ∃ constants : ℕ→ℝ,(∀ grade,0≤constants grade) ∧
      ∀ (core image : ACore parameters 3),
      originalSourceFieldLinear parameters image=
        originalCircleKernel (originalSourceFieldLinear parameters core) →
      ∀ grade,originalCellNorm parameters grade image≤constants grade*originalCellNorm parameters grade core := by
  let endpoint := fun grade => (StartupSpatialAction.circle_originalEndpointControlled (L:=1) (ell:=1) parameters grade).2
  refine ⟨(fun grade => (endpoint grade).choose),(fun grade => (endpoint grade).choose_spec.1),?_⟩
  intro core image same grade
  by_contra failure
  have strict := lt_of_not_ge failure
  let gap := originalCellNorm parameters grade image-(endpoint grade).choose*originalCellNorm parameters grade core
  have gapPositive : 0<gap := sub_pos.mpr strict
  let magnitude := originalGradeNorm grade core
  have magnitudeNonnegative : 0≤magnitude := originalGradeNorm_nonnegative grade core
  let epsilon := gap/(2*(magnitude+1))
  have denominatorPositive : 0<2*(magnitude+1) := by positivity
  have epsilonPositive : 0<epsilon := div_pos gapPositive denominatorPositive
  let estimate := (endpoint grade).choose_spec.2 epsilon epsilonPositive
  have bounded := estimate.choose_spec.2 (⟨0,le_rfl⟩ : {value : ℝ // 0≤value}) core image same
  have paid : originalCellNorm parameters grade image≤
      (endpoint grade).choose*originalCellNorm parameters grade core+epsilon*magnitude := by
    simpa only [zero_mul,mul_zero,add_zero] using bounded
  have exactEpsilon : epsilon*(2*(magnitude+1))=gap :=
    div_mul_cancel₀ gap (ne_of_gt denominatorPositive)
  dsimp only [gap] at exactEpsilon
  nlinarith only [paid,exactEpsilon,epsilonPositive,magnitudeNonnegative]

end Grad.OriginalCoreRealization
