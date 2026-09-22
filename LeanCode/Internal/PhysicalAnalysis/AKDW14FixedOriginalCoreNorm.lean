import AKDW10OriginalUnitNativeFluxEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.CartesianStartup.StartupSpatialAction
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.NonlinearProduct
open Grad.OriginalCoreRealization

/-- A fixed genuine angular/spatial action constructs its original image. -/
theorem fixedCore_exists {input output rank : ℕ} (parameters : PhaseParameters)
    (operator : StartupSpatialAction rank input output 1 1) (controlled : operator.OriginalEndpointControlled parameters)
    (core : ACore parameters input) :
    ∃ image : ACore parameters output,originalSourceFieldLinear parameters image=operator.signed.coarse (originalSourceFieldLinear parameters core) := by
  let actual := (controlled.1.choose_spec (⟨0,le_rfl⟩ : {value : ℝ // 0≤value})).some
  exact ⟨actual.action core,actual.same core⟩

/-- Same-field norm fidelity for a fixed action, with no coefficient or
unknown base factor introduced into a known-source estimate. -/
theorem fixedCore_bound {input output rank : ℕ} (parameters : PhaseParameters)
    (operator : StartupSpatialAction rank input output 1 1) (controlled : operator.OriginalEndpointControlled parameters) :
    ∃ constant : ℝ,0≤constant ∧ ∀ (core : ACore parameters input) (image : ACore parameters output),
      originalSourceFieldLinear parameters image=operator.signed.coarse (originalSourceFieldLinear parameters core) →
      originalGradeNorm rank image≤constant*originalGradeNorm rank core := by
  let profile := controlled.1.choose
  let actual := (controlled.1.choose_spec (⟨0,le_rfl⟩ : {value : ℝ // 0≤value})).some
  refine ⟨profile.high,profile.highNonnegative,?_⟩
  intro core image same
  have identical : image=actual.action core := originalSourceFieldLinear_injective parameters (same.trans (actual.same core).symm)
  rw [identical]
  simpa only [zero_mul,add_zero] using actual.highBound core

end Grad.CartesianStartup.StartupSpatialAction
