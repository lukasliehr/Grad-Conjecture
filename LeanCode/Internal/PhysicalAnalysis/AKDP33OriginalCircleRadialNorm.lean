import AKDP27ActualFixedFormulaRankControl
import AKDR9ActualRetainedScalarRecoveryNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.NonlinearProduct
open Grad.OriginalCoreRealization Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- Any fixed actual formula constructs its original core at the same
width. Its rank profile at budget zero gives the same-grade norm bound. -/
theorem StartupSpatialAction.OriginalRankControlled.core_bound {input output rank : ℕ}
    {parameters : PhaseParameters} {L ell : ℝ} {operator : StartupSpatialAction rank input output L ell}
    (actual : operator.OriginalRankControlled parameters) :
    ∃ constant : ℝ,0≤constant ∧ ∀ core : ACore parameters input,
      ∃ image : ACore parameters output,
        originalSourceFieldLinear parameters image=operator.signed.coarse (originalSourceFieldLinear parameters core) ∧
        originalGradeNorm rank image≤constant*originalGradeNorm rank core := by
  obtain ⟨profile,controlled⟩ := actual
  let result := (controlled ⟨0,le_rfl⟩).some
  refine ⟨profile.high,profile.highNonnegative,fun core => ⟨result.action core,result.same core,?_⟩⟩
  simpa only [zero_mul,add_zero] using result.highBound core

theorem StartupSpatialAction.OriginalRankControlled.sameCore_bound {input output rank : ℕ}
    {parameters : PhaseParameters} {L ell : ℝ} {operator : StartupSpatialAction rank input output L ell}
    (actual : operator.OriginalRankControlled parameters) :
    ∃ constant : ℝ,0≤constant ∧ ∀ (core : ACore parameters input) (image : ACore parameters output),
      originalSourceFieldLinear parameters image=operator.signed.coarse (originalSourceFieldLinear parameters core) →
      originalGradeNorm rank image≤constant*originalGradeNorm rank core := by
  obtain ⟨constant,nonnegative,bounded⟩ := actual.core_bound
  refine ⟨constant,nonnegative,?_⟩
  intro core image same
  obtain ⟨actualImage,identified,bound⟩ := bounded core
  have identity := originalSourceFieldLinear_injective parameters (same.trans identified.symm)
  simpa only [identity] using bound

/-- The actual circle projection on SAME original cores, with no
admissibility or physical-length-at-unit-scale assumption. -/
theorem startupOriginalCircle_core_bound (parameters : PhaseParameters) (rank : ℕ) :
    ∃ constant : ℝ,0≤constant ∧ ∀ (core image : ACore parameters 3),
      originalSourceFieldLinear parameters image=originalCircleKernel (originalSourceFieldLinear parameters core) →
      originalGradeNorm rank image≤constant*originalGradeNorm rank core :=
  (StartupSpatialAction.circle_originalRankControlled (L := 1) (ell := 1) parameters rank).sameCore_bound

theorem startupOriginalCircle_core_exists (parameters : PhaseParameters) (core : ACore parameters 3) :
    ∃ image : ACore parameters 3,
      originalSourceFieldLinear parameters image=originalCircleKernel (originalSourceFieldLinear parameters core) := by
  obtain ⟨_,_,bounded⟩ := (StartupSpatialAction.circle_originalRankControlled (L := 1) (ell := 1) parameters 0).core_bound
  obtain ⟨image,same,_⟩ := bounded core
  exact ⟨image,same⟩

/-- The genuine radial projector has the same original-core estimate. -/
theorem startupOriginalQrad_core_bound (parameters : PhaseParameters) (rank : ℕ) :
    ∃ constant : ℝ,0≤constant ∧ ∀ (core image : ACore parameters 2),
      originalSourceFieldLinear parameters image=startupGenuineQradKernel (originalSourceFieldLinear parameters core) →
      originalGradeNorm rank image≤constant*originalGradeNorm rank core :=
  (StartupSpatialAction.radial_originalRankControlled (L := 1) (ell := 1) parameters rank).sameCore_bound

theorem startupOriginalQrad_core_exists (parameters : PhaseParameters) (core : ACore parameters 2) :
    ∃ image : ACore parameters 2,
      originalSourceFieldLinear parameters image=startupGenuineQradKernel (originalSourceFieldLinear parameters core) := by
  obtain ⟨_,_,bounded⟩ := (StartupSpatialAction.radial_originalRankControlled (L := 1) (ell := 1) parameters 0).core_bound
  obtain ⟨image,same,_⟩ := bounded core
  exact ⟨image,same⟩

end Grad.CartesianStartup
