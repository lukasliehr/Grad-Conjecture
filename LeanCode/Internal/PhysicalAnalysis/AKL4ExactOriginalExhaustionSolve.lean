import AKL3IndependentZeroBoundaryData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularExhaustionEstimate
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularForwardDatum Grad.AnnularForwardTraces Grad.AnnularStrongOrbit
open Grad.AnnularHighGenerators Grad.AnnularCrossOrbit Grad.AnnularCoupledInverse
attribute [local instance] Grad.AnnularStrongOrbit.knownAmbientNormed Grad.AnnularStrongOrbit.knownAmbientSeminormed Grad.AnnularStrongOrbit.knownAmbientRealNormed Grad.AnnularStrongOrbit.knownAmbientRealModule
  Grad.AnnularStrongOrbit.strongCarrierNormed Grad.AnnularStrongOrbit.strongCarrierSeminormed Grad.AnnularStrongOrbit.strongCarrierRealNormed Grad.AnnularStrongOrbit.strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace
  Grad.AnnularCrossOrbit.coupledNormed Grad.AnnularCrossOrbit.coupledSeminormed
  Grad.AnnularCrossOrbit.coupledComplexNormed Grad.AnnularCrossOrbit.coupledComplexModule
  Grad.AnnularCrossOrbit.coupledRealNormed Grad.AnnularCrossOrbit.coupledRealModule
  Grad.AnnularCrossOrbit.coupledOperatorRealNormed Grad.AnnularCrossOrbit.coupledOperatorRealModule



variable (parameters : PhaseParameters) (length compact : ℝ)

/-- The actual full original annular inverse used by exhaustion, with all
copied sources and full residuals and independent homogeneous boundary data. -/
def originalExhaustionSolve (context : CoupledCoordinateContext parameters length compact)
    (data : OriginalStrongCarrier parameters context.lower 0 0) :
    ForwardFiveBlocks parameters context.lower length context.positive :=
  originalSolvedFiveBlock parameters length compact context.lower context.positive context.lowerHalf
    context.lengthPositive context.state context.widthHalf context.widthLength context.small
    (zeroBoundaryDatum parameters context.lower data)

def exhaustionDatumNorm (context : CoupledCoordinateContext parameters length compact)
    (data : OriginalStrongCarrier parameters context.lower 0 0) : ℝ :=
  originalWeightedDatumNorm parameters context.lower length context.positive
    (context.lowerHalf.trans (by norm_num)) context.lengthPositive
    (zeroBoundaryDatum parameters context.lower data)

def ExhaustionDataInserted (context : CoupledCoordinateContext parameters length compact)
    (grade : ℕ) (data : OriginalStrongCarrier parameters context.lower 0 0)
    (weighted : StrongDataCarrier parameters context.lower context.positive
      (context.lowerHalf.trans (by norm_num)) 0 0) : Prop :=
  StrongInsertedGrade parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) grade
    (originalWeightedDatum parameters context.lower length context.positive
      (context.lowerHalf.trans (by norm_num)) context.lengthPositive
      (zeroBoundaryDatum parameters context.lower data)) weighted

def ExhaustionRetainedInserted (context : CoupledCoordinateContext parameters length compact)
    (grade : ℕ) (data : OriginalStrongCarrier parameters context.lower 0 0)
    (weighted : CoupledSpace context.lower length context.positive context.lengthPositive) : Prop :=
  CoupledInsertedGrade context.lower length context.positive context.lengthPositive grade
    (originalWeightedRetained parameters context.lower length context.positive
      (context.lowerHalf.trans (by norm_num)) context.lengthPositive
      (originalExhaustionSolve parameters length compact context data).ofLp.1) weighted

theorem originalExhaustionSolve_sources (context : CoupledCoordinateContext parameters length compact)
    (data : OriginalStrongCarrier parameters context.lower 0 0) :
    (originalExhaustionSolve parameters length compact context data).ofLp.2 = data.val.ofLp.1 := rfl

theorem originalExhaustionSolve_boundary (context : CoupledCoordinateContext parameters length compact)
    (data : OriginalStrongCarrier parameters context.lower 0 0) :
    originalBoundaryTrace parameters length compact context.lower context.positive context.lowerHalf
      context.lengthPositive context.state
      ((originalExhaustionSolve parameters length compact context data).ofLp.1,
        (originalExhaustionSolve parameters length compact context data).ofLp.2.ofLp.1) = 0 :=
  zeroBoundaryDatum_response_traces parameters length compact context data

theorem originalExhaustionSolve_equation (context : CoupledCoordinateContext parameters length compact)
    (data : OriginalStrongCarrier parameters context.lower 0 0) :
    OriginalStrongCoupledEquation parameters length compact context.lower context.positive context.lowerHalf
      context.lengthPositive context.widthHalf context.widthLength context.state
      (zeroBoundaryDatum parameters context.lower data)
      (originalExhaustionSolve parameters length compact context data).ofLp.1 :=
  originalSharedResponse_equation parameters length compact context.lower context.positive context.lowerHalf
    context.lengthPositive context.widthHalf context.widthLength context.state context.small
    (zeroBoundaryDatum parameters context.lower data)

/-- EX's native weighted estimate for the SAME original full solve. The
constant is independent of the moving inner radius and unrestricted high
state norms; the only high state factor is the original B_(8+t). -/
theorem originalExhaustionSolve_uniform (lengthPositive : 0 < length) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (context : CoupledCoordinateContext parameters length compact)
        (data : OriginalStrongCarrier parameters context.lower 0 0)
        (weighted : StrongDataCarrier parameters context.lower context.positive
          (context.lowerHalf.trans (by norm_num)) 0 0)
        (_inserted : ExhaustionDataInserted parameters length compact context grade data weighted),
        ∃ retained : CoupledSpace context.lower length context.positive context.lengthPositive,
          ExhaustionRetainedInserted parameters length compact context grade data retained ∧
          ‖retained‖ ≤ constant * (‖weighted‖ + context.budget grade *
            exhaustionDatumNorm parameters length compact context data) := by
  let certificate := originalSharedResponse_uniform_inserted parameters length compact lengthPositive grade
  refine ⟨certificate.choose, certificate.choose_spec.1, ?_⟩
  intro context data weighted inserted
  exact certificate.choose_spec.2 context (zeroBoundaryDatum parameters context.lower data) weighted inserted

end Grad.AnnularExhaustionEstimate
