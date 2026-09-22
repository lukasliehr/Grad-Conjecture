import AKDP49AdjustableCellComposition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.NonlinearProduct
open Grad.OriginalCartesianTameEstimate Grad.OriginalCoreRealization

/-- Both genuine endpoints of a uniform actual original-core action. -/
def StartupUniformOriginalEndpoint {State : Type*} {input output rank : ℕ}
    (parameters : PhaseParameters) (budget : State → ℝ)
    (kernel : State → StartupL2 input →L[ℂ] StartupL2 output)
    (ranked : State → StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension output rank)) : Prop :=
  StartupUniformOriginalRank parameters budget kernel ranked ∧ StartupUniformOriginalCell parameters rank budget kernel

namespace StartupUniformOriginalEndpoint
variable {State : Type*} {input output rank : ℕ} {parameters : PhaseParameters} {budget : State → ℝ}
    {firstKernel secondKernel : State → StartupL2 input →L[ℂ] StartupL2 output}
    {firstRank secondRank : State → StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension output rank)}

theorem add (first : StartupUniformOriginalEndpoint parameters budget firstKernel firstRank)
    (second : StartupUniformOriginalEndpoint parameters budget secondKernel secondRank) :
    StartupUniformOriginalEndpoint parameters budget (fun state => firstKernel state+secondKernel state)
      (fun state => firstRank state+secondRank state) := by
  refine ⟨first.1.add second.1,?_⟩
  obtain ⟨firstLeading,firstNonnegative,firstBound⟩ := first.2
  obtain ⟨secondLeading,secondNonnegative,secondBound⟩ := second.2
  obtain ⟨_,firstControls⟩ := first.1
  obtain ⟨_,secondControls⟩ := second.1
  refine ⟨firstLeading+secondLeading,add_nonneg firstNonnegative secondNonnegative,?_⟩
  intro epsilon positive
  obtain ⟨firstTail,firstTailNonnegative,firstEstimate⟩ := firstBound (epsilon/2) (by positivity)
  obtain ⟨secondTail,secondTailNonnegative,secondEstimate⟩ := secondBound (epsilon/2) (by positivity)
  refine ⟨firstTail+secondTail,add_nonneg firstTailNonnegative secondTailNonnegative,?_⟩
  intro state core image same
  let one := (firstControls state).some
  let two := (secondControls state).some
  have imageSame : image=one.action core+two.action core := by
    apply originalSourceFieldLinear_injective parameters
    rw [map_add,one.same,two.same]
    exact same
  rw [imageSame]
  exact (startupOriginalCellNorm_add parameters rank (one.action core) (two.action core)).trans
    ((add_le_add (firstEstimate state core (one.action core) (one.same core))
      (secondEstimate state core (two.action core) (two.same core))).trans_eq (by ring))

theorem sub (first : StartupUniformOriginalEndpoint parameters budget firstKernel firstRank)
    (second : StartupUniformOriginalEndpoint parameters budget secondKernel secondRank) :
    StartupUniformOriginalEndpoint parameters budget (fun state => firstKernel state-secondKernel state)
      (fun state => firstRank state-secondRank state) := by
  refine ⟨first.1.sub second.1,?_⟩
  obtain ⟨firstLeading,firstNonnegative,firstBound⟩ := first.2
  obtain ⟨secondLeading,secondNonnegative,secondBound⟩ := second.2
  obtain ⟨_,firstControls⟩ := first.1
  obtain ⟨_,secondControls⟩ := second.1
  refine ⟨firstLeading+secondLeading,add_nonneg firstNonnegative secondNonnegative,?_⟩
  intro epsilon positive
  obtain ⟨firstTail,firstTailNonnegative,firstEstimate⟩ := firstBound (epsilon/2) (by positivity)
  obtain ⟨secondTail,secondTailNonnegative,secondEstimate⟩ := secondBound (epsilon/2) (by positivity)
  refine ⟨firstTail+secondTail,add_nonneg firstTailNonnegative secondTailNonnegative,?_⟩
  intro state core image same
  let one := (firstControls state).some
  let two := (secondControls state).some
  have imageSame : image=one.action core-two.action core := by
    apply originalSourceFieldLinear_injective parameters
    rw [map_sub,one.same,two.same]
    exact same
  rw [imageSame]
  exact (startupOriginalCellNorm_sub parameters rank (one.action core) (two.action core)).trans
    ((add_le_add (firstEstimate state core (one.action core) (one.same core))
      (secondEstimate state core (two.action core) (two.same core))).trans_eq (by ring))

theorem comp {middle : ℕ}
    {outerKernel : State → StartupL2 middle →L[ℂ] StartupL2 output}
    {innerKernel : State → StartupL2 input →L[ℂ] StartupL2 middle}
    {outerRank : State → StartupL2 (startupTensorDimension middle rank) →L[ℂ] StartupL2 (startupTensorDimension output rank)}
    {innerRank : State → StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension middle rank)}
    (outer : StartupUniformOriginalEndpoint parameters budget outerKernel outerRank)
    (inner : StartupUniformOriginalEndpoint parameters budget innerKernel innerRank)
    (outerBound : ℝ) (outerNonnegative : 0≤outerBound) (bounded : ∀ state,‖outerRank state‖≤outerBound)
    (budgetNonnegative : ∀ state,0≤budget state) :
    StartupUniformOriginalEndpoint parameters budget (fun state => (outerKernel state).comp (innerKernel state))
      (fun state => (outerRank state).comp (innerRank state)) :=
  ⟨outer.1.comp inner.1 outerBound outerNonnegative bounded budgetNonnegative,
    outer.2.comp inner.2 inner.1 budgetNonnegative⟩

end StartupUniformOriginalEndpoint
end Grad.CartesianStartup
