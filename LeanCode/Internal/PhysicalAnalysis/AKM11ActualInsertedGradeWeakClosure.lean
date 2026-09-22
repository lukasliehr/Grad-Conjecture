import AKM10OriginalRestrictionWeakLimits

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.AnnularWeakExhaustion
open Grad.AnnularVariational Grad.AnnularOmegaGraph Grad.AnnularCoupledInverse
open Grad.AnnularHighGenerators Grad.AnnularCrossMaps Grad.AnnularLowEnergy Grad.AnnularLowOrbit Grad.AnnularLowCompletion
open Grad.AnnularForwardTraces Grad.AnnularStrongOrbit Grad.SourceCollarDivision
attribute [local instance] traceCoupledRealNormed traceCoupledRealModule

/-- A genuine coordinate identity passes through weak limits of both fields. -/
theorem weakLimit_mapped_relation {E F H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {first : ℕ → E} {second : ℕ → F} {firstLimit : E} {secondLimit : F}
    (one : WeakConverges first firstLimit) (two : WeakConverges second secondLimit)
    (left : E →L[ℝ] H) (right : F →L[ℝ] H)
    (same : ∀ᶠ n in atTop, left (first n) = right (second n)) :
    left firstLimit = right secondLimit :=
  ((one.map left).congr same).unique (two.map right)

local instance weakModeEnergyRealInner (lower : ℝ) :
    InnerProductSpace ℝ (AnnularModeEnergyAmbient lower) :=
  InnerProductSpace.rclikeToReal ℂ (AnnularModeEnergyAmbient lower)
local instance weakRadialRealInner (lower : ℝ) : InnerProductSpace ℝ (RadialL2 1 lower) :=
  InnerProductSpace.rclikeToReal ℂ (RadialL2 1 lower)

variable (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)

/-- Exact fixed-mode observation of the whole genuine high energy graph. -/
def coupledEnergyMode (index : HighAnnularMode) :
    CoupledSpace lower length positive lengthPositive →L[ℝ] AnnularModeEnergyAmbient lower :=
  (((lp.evalCLM ℂ (fun _ : HighAnnularMode => AnnularModeEnergyAmbient lower) 2 index).comp
    (annularEnergySpace lower length positive).subtypeL).comp
      (coupledEnergy lower length positive lengthPositive)).restrictScalars ℝ

/-- Both genuine flux coordinates, without forgetting its weak derivative. -/
def coupledFluxMode (coordinate : Fin 2) (index : HighAnnularMode) :
    CoupledSpace lower length positive lengthPositive →L[ℝ] RadialL2 1 lower :=
  (((lp.evalCLM ℂ _ 2 index).comp
    (fluxStoredCoordinate lower length positive lengthPositive coordinate)).comp
      (coupledFlux lower length positive lengthPositive)).restrictScalars ℝ

/-- Both rho-balanced stored low coordinates and all actual low modes. -/
def coupledLowMode (coordinate : Fin 2) (index : LowAnnularIndex) :
    CoupledSpace lower length positive lengthPositive →L[ℝ] RadialL2 1 lower :=
  (((lp.evalCLM ℂ _ 2 index).comp
    (lowStoredCoordinate lower length positive coordinate)).comp
      (coupledLow lower length positive lengthPositive)).restrictScalars ℝ

theorem coupledEnergyMode_apply (index : HighAnnularMode) (field : CoupledSpace lower length positive lengthPositive) :
    coupledEnergyMode lower length positive lengthPositive index field = field.ofLp.1.ofLp.1.val index := by
  rfl
theorem coupledFluxMode_apply (coordinate : Fin 2) (index : HighAnnularMode) (field : CoupledSpace lower length positive lengthPositive) :
    coupledFluxMode lower length positive lengthPositive coordinate index field = field.ofLp.1.ofLp.2.val coordinate index := by
  rfl
theorem coupledLowMode_apply (coordinate : Fin 2) (index : LowAnnularIndex) (field : CoupledSpace lower length positive lengthPositive) :
    coupledLowMode lower length positive lengthPositive coordinate index field = field.ofLp.2.val coordinate index := by
  rfl

/-- Literal BF inserted-grade witnesses are weakly closed for the SAME
retained field. No claim that an inserted field satisfies the unchanged PDE
is used: every energy, flux and low identity follows from its actual CLM. -/
theorem coupledInsertedGrade_weak_limit (grade : ℕ)
    {sequence inserted : ℕ → CoupledSpace lower length positive lengthPositive}
    {limit insertedLimit : CoupledSpace lower length positive lengthPositive}
    (one : WeakConverges sequence limit) (two : WeakConverges inserted insertedLimit)
    (same : ∀ᶠ n in atTop, CoupledInsertedGrade lower length positive lengthPositive grade (sequence n) (inserted n)) :
    CoupledInsertedGrade lower length positive lengthPositive grade limit insertedLimit := by
  refine ⟨?_,?_,?_⟩
  · intro index
    let observation := coupledEnergyMode lower length positive lengthPositive index
    have identity := weakLimit_mapped_relation two one observation
      (((Grad.AnnularVariational.annularFrequency index.val.1 index.val.2 ^ grade : ℝ) : ℂ) • observation)
      (same.mono (fun n law => by
        change observation (inserted n) = ((Grad.AnnularVariational.annularFrequency index.val.1 index.val.2 ^ grade : ℝ) : ℂ) • observation (sequence n)
        simpa only [observation, coupledEnergyMode_apply] using law.1 index))
    change observation insertedLimit = ((Grad.AnnularVariational.annularFrequency index.val.1 index.val.2 ^ grade : ℝ) : ℂ) • observation limit at identity
    simpa only [observation, coupledEnergyMode_apply] using identity
  · intro coordinate index
    let observation := coupledFluxMode lower length positive lengthPositive coordinate index
    have identity := weakLimit_mapped_relation two one observation
      (((Grad.AnnularVariational.annularFrequency index.val.1 index.val.2 ^ grade : ℝ) : ℂ) • observation)
      (same.mono (fun n law => by
        change observation (inserted n) = ((Grad.AnnularVariational.annularFrequency index.val.1 index.val.2 ^ grade : ℝ) : ℂ) • observation (sequence n)
        simpa only [observation, coupledFluxMode_apply] using law.2.1 coordinate index))
    change observation insertedLimit = ((Grad.AnnularVariational.annularFrequency index.val.1 index.val.2 ^ grade : ℝ) : ℂ) • observation limit at identity
    simpa only [observation, coupledFluxMode_apply] using identity
  · intro coordinate index
    let observation := coupledLowMode lower length positive lengthPositive coordinate index
    have identity := weakLimit_mapped_relation two one observation
      (((lowInsertedFrequency index ^ grade : ℝ) : ℂ) • observation)
      (same.mono (fun n law => by
        change observation (inserted n) = ((lowInsertedFrequency index ^ grade : ℝ) : ℂ) • observation (sequence n)
        simpa only [observation, coupledLowMode_apply] using law.2.2 coordinate index))
    change observation insertedLimit = ((lowInsertedFrequency index ^ grade : ℝ) : ℂ) • observation limit at identity
    simpa only [observation, coupledLowMode_apply] using identity

end Grad.AnnularWeakExhaustion
