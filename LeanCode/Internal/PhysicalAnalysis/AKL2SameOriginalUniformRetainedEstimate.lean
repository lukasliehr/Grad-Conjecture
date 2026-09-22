import AKL1LiteralExhaustionWeightedNorms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularExhaustionEstimate
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularForwardDatum Grad.AnnularForwardTraces Grad.AnnularStrongOrbit
open Grad.AnnularHighGenerators Grad.AnnularCrossOrbit Grad.AnnularCoupledInverse
open Grad.AnnularFullSource Grad.GaugeCoefficients.Physical.Allocation
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



private theorem transferRelation {E : Type*} (relation : E → E → Prop)
    {first second weighted : E} (same : first = second) (actual : relation second weighted) :
    relation first weighted := same.symm ▸ actual

variable (parameters : PhaseParameters) (length compact : ℝ)

theorem originalWeightedRetained_sameResponse
    (context : CoupledCoordinateContext parameters length compact)
    (data : OriginalStrongCarrier parameters context.lower 0 0) :
    originalWeightedRetained parameters context.lower length context.positive
      (context.lowerHalf.trans (by norm_num)) context.lengthPositive
      (originalSharedResponse parameters length compact context.lower context.positive context.lowerHalf
        context.lengthPositive context.widthHalf context.widthLength context.state context.small data) =
      sharedStrongResponse parameters length compact context.lower context.positive context.lowerHalf
        context.lengthPositive context.widthHalf context.widthLength context.state context.small
        (originalWeightedDatum parameters context.lower length context.positive
          (context.lowerHalf.trans (by norm_num)) context.lengthPositive data) :=
  originalSharedResponse_weighted parameters length compact context.lower context.positive context.lowerHalf
    context.lengthPositive context.widthHalf context.widthLength context.state context.small data

/-- The radius-uniform base estimate in the literal weighted retained norm,
for the same original inverse and every independently prescribed datum. -/
theorem originalSharedResponse_uniform_base
    (context : CoupledCoordinateContext parameters length compact)
    (data : OriginalStrongCarrier parameters context.lower 0 0) :
    originalWeightedRetainedNorm parameters context.lower length context.positive
      (context.lowerHalf.trans (by norm_num)) context.lengthPositive
      (originalSharedResponse parameters length compact context.lower context.positive context.lowerHalf
        context.lengthPositive context.widthHalf context.widthLength context.state context.small data) ≤
      2 * independentCoupledDataConstant parameters length compact *
        originalWeightedDatumNorm parameters context.lower length context.positive
          (context.lowerHalf.trans (by norm_num)) context.lengthPositive data := by
  let input := originalWeightedDatum parameters context.lower length context.positive
    (context.lowerHalf.trans (by norm_num)) context.lengthPositive data
  have estimate := sharedStrongResponse_bound parameters length compact context.lower context.positive context.lowerHalf
    context.lengthPositive context.widthHalf context.widthLength context.state context.small input
  have normSame := congrArg
    (fun field : CoupledSpace context.lower length context.positive context.lengthPositive => ‖field‖)
    (originalWeightedRetained_sameResponse parameters length compact context data)
  exact normSame.trans_le estimate

/-- Every literal inserted data grade gives membership of the SAME original
solution and a constant chosen before the collar and retained state. -/
theorem originalSharedResponse_uniform_inserted (lengthPositive : 0 < length) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (context : CoupledCoordinateContext parameters length compact)
        (data : OriginalStrongCarrier parameters context.lower 0 0)
        (dataWeighted : StrongDataCarrier parameters context.lower context.positive
          (context.lowerHalf.trans (by norm_num)) 0 0)
        (_inserted : StrongInsertedGrade parameters context.lower context.positive
          (context.lowerHalf.trans (by norm_num)) grade
          (originalWeightedDatum parameters context.lower length context.positive
            (context.lowerHalf.trans (by norm_num)) context.lengthPositive data) dataWeighted),
        ∃ retainedWeighted : CoupledSpace context.lower length context.positive context.lengthPositive,
          CoupledInsertedGrade context.lower length context.positive context.lengthPositive grade
            (originalWeightedRetained parameters context.lower length context.positive
              (context.lowerHalf.trans (by norm_num)) context.lengthPositive
              (originalSharedResponse parameters length compact context.lower context.positive context.lowerHalf
                context.lengthPositive context.widthHalf context.widthLength context.state context.small data)) retainedWeighted ∧
          ‖retainedWeighted‖ ≤ constant * (‖dataWeighted‖ + context.budget grade *
            originalWeightedDatumNorm parameters context.lower length context.positive
              (context.lowerHalf.trans (by norm_num)) context.lengthPositive data) := by
  let certificate := sameSharedInverse_inserted_tame parameters length compact lengthPositive grade
  refine ⟨certificate.choose, certificate.choose_spec.1, ?_⟩
  intro context data dataWeighted inserted
  let input := originalWeightedDatum parameters context.lower length context.positive
    (context.lowerHalf.trans (by norm_num)) context.lengthPositive data
  let result := certificate.choose_spec.2 context input dataWeighted inserted
  refine ⟨result.choose, ?_, result.choose_spec.2⟩
  exact transferRelation (CoupledInsertedGrade context.lower length context.positive context.lengthPositive grade)
    (originalWeightedRetained_sameResponse parameters length compact context data) result.choose_spec.1

end Grad.AnnularExhaustionEstimate
