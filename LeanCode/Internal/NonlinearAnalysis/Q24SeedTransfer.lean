import Q24CompletedChart
import TameCompositionState

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped ContDiff

namespace Grad.Q24Realization

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearQuotientBounds Grad.NonlinearProduct
open Grad.Constraints Grad.SmoothingFamily Grad.AxisCore Grad.ImplementationReadiness

def seedTransferCoreLinear (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) :
    GradeCore parameters 3 grade →ₗ[ℂ] AGrade parameters 3 grade :=
  (fieldEmbed parameters 3 grade).comp
    ((Gauges.seedTransfer parameters reference insideR seed insideS).comp GradeCore.toCoreLinear)

def seedTransferCoreContinuous (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) :
    GradeCore parameters 3 grade →L[ℂ] AGrade parameters 3 grade :=
  (seedTransferCoreLinear parameters reference insideR seed insideS grade).mkContinuous
    |Gauges.seedTransferGradeConstant parameters reference seed grade| (fun field => by
      change ‖fieldEmbed parameters 3 grade
        (Gauges.seedTransfer parameters reference insideR seed insideS field.toCore)‖ ≤ _
      rw [fieldEmbed_norm]
      simpa only [originalGradeNorm, GradeCore.ofCore_toCore] using
        originalGradeNorm_seedTransfer_le reference insideR seed insideS grade field.toCore)

/-- Actual N18 ambient transfer, extended in the identical original grade. -/
def completedSeedTransfer (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) :
    AGrade parameters 3 grade →L[ℂ] AGrade parameters 3 grade :=
  (seedTransferCoreContinuous parameters reference insideR seed insideS grade).fromCompletion

theorem completedSeedTransfer_core (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (field : ACore parameters 3) :
    completedSeedTransfer parameters reference insideR seed insideS grade
      (fieldEmbed parameters 3 grade field) =
    fieldEmbed parameters 3 grade (Gauges.seedTransfer parameters reference insideR seed insideS field) :=
  ContinuousLinearMap.fromCompletion_apply_coe _ (GradeCore.ofCoreLinear field)

theorem completedSeedTransfer_bound (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (field : AGrade parameters 3 grade) :
    ‖completedSeedTransfer parameters reference insideR seed insideS grade field‖ ≤
      |Gauges.seedTransferGradeConstant parameters reference seed grade| * ‖field‖ := by
  refine isClosed_property (aGradeEta_denseRange parameters)
    (isClosed_le (completedSeedTransfer parameters reference insideR seed insideS grade).continuous.norm
      (continuous_const.mul continuous_norm)) ?_ field
  intro core
  change ‖completedSeedTransfer parameters reference insideR seed insideS grade
    (fieldEmbed parameters 3 grade core.toCore)‖ ≤
      |Gauges.seedTransferGradeConstant parameters reference seed grade| *
        ‖fieldEmbed parameters 3 grade core.toCore‖
  rw [completedSeedTransfer_core, fieldEmbed_norm, fieldEmbed_norm]
  simpa only [originalGradeNorm, GradeCore.ofCore_toCore] using
    originalGradeNorm_seedTransfer_le reference insideR seed insideS grade core.toCore

def completedReferenceTransfer (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (state : XAmbient parameters grade) : XAmbient parameters grade :=
  statePack state.ofLp.1
    (completedSeedTransfer parameters reference insideR seed insideS grade state.ofLp.2.ofLp.1)
    state.ofLp.2.ofLp.2

theorem completedReferenceTransfer_contDiff (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) :
    ContDiff ℝ ∞ (completedReferenceTransfer parameters reference insideR seed insideS grade) := by
  have fieldSmooth := ((completedSeedTransfer parameters reference insideR seed insideS grade).restrictScalars ℝ).contDiff.comp
    (stateFields_contDiff parameters grade).fst
  exact (WithLp.prodContinuousLinearEquiv 1 ℝ (AxisGrade parameters 2 (grade + 1))
    (WithLp 1 (AGrade parameters 3 grade × AGrade parameters 1 grade))).symm.contDiff.comp
      ((stateAxis_contDiff parameters grade).prodMk
        ((WithLp.prodContinuousLinearEquiv 1 ℝ (AGrade parameters 3 grade) (AGrade parameters 1 grade)).symm.contDiff.comp
          (fieldSmooth.prodMk (stateFields_contDiff parameters grade).snd)))

theorem completedReferenceTransfer_core (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (state : ChartState parameters) :
    completedReferenceTransfer parameters reference insideR seed insideS grade
      (chartCoreEmbed parameters grade state) =
    chartCoreEmbed parameters grade (referenceTransfer parameters reference insideR seed insideS state) := by
  unfold completedReferenceTransfer chartCoreEmbed
  simp only [statePack, WithLp.ofLp_toLp, completedSeedTransfer_core, referenceTransfer_apply]

end Grad.Q24Realization
