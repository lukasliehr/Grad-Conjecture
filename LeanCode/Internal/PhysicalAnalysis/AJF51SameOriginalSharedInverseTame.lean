import AJF49GeneralSharedResponseTame
import AJF50ActualSharedResponseCoordinateBounds
import AJF41LiteralInsertedDecode
import AJF36ActualApplicationTameConvolution
import AJF30AugmentedCoordinateBudget
import AJE54CompleteSourceOneHighBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open scoped ContDiff BigOperators
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularReconstruction Grad.CartesianState Grad.AnnularKernelOrbit
open Grad.AnnularStrongData Grad.AnnularStrongOrbit Grad.AnnularCoupledOrbit Grad.AnnularCoupledInverse
open Grad.AnnularLowEnergy Grad.AnnularLowOrbit Grad.AnnularCurrentLow Grad.AnnularKnownLow
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCurrentSource Grad.AnnularStrongSolution
open Grad.AnnularCrossMaps Grad.AnnularFullSource Grad.AnnularCrossOrbit

attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace
  Grad.AnnularCrossOrbit.coupledNormed Grad.AnnularCrossOrbit.coupledSeminormed
  Grad.AnnularCrossOrbit.coupledComplexNormed Grad.AnnularCrossOrbit.coupledComplexModule
  Grad.AnnularCrossOrbit.coupledRealNormed Grad.AnnularCrossOrbit.coupledRealModule
  Grad.AnnularCrossOrbit.coupledOperatorRealNormed Grad.AnnularCrossOrbit.coupledOperatorRealModule

/-- The SAME full independently prescribed coupled inverse satisfies the
original literal ν tame estimate on its unchanged B8 ball. The single constant
precedes the original context, including the inner radius and retained state. -/
theorem sameSharedInverse_inserted_tame (parameters : PhaseParameters) (L compact : ℝ)
    (lengthPositive : 0 < L) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (context : CoupledCoordinateContext parameters L compact)
      (data weighted : StrongDataCarrier parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) 0 0)
      (_actual : StrongInsertedGrade parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) grade data weighted),
      ∃ solutionWeighted : CoupledSpace context.lower L context.positive context.lengthPositive,
        CoupledInsertedGrade context.lower L context.positive context.lengthPositive grade
          (sharedStrongResponse parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state context.small data) solutionWeighted ∧
        ‖solutionWeighted‖ ≤ constant * (‖weighted‖ + context.budget grade * ‖data‖) :=
  generalSharedResponse_inserted_tame parameters L compact
    (sharedResponseCoordinateFamily_uniformCoordinateBound parameters L compact lengthPositive) grade

/-- Every original inserted source grade gives every original inserted
solution grade of this one constructed field. No extra inverse is selected. -/
theorem sameSharedInverse_allInsertedGrades (parameters : PhaseParameters) (L compact : ℝ)
    (context : CoupledCoordinateContext parameters L compact)
    (data : StrongDataCarrier parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) 0 0)
    (grades : ∀ grade : ℕ, ∃ weighted : StrongDataCarrier parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) 0 0,
      StrongInsertedGrade parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) grade data weighted) :
    ∀ grade : ℕ, ∃ weighted : CoupledSpace context.lower L context.positive context.lengthPositive,
      CoupledInsertedGrade context.lower L context.positive context.lengthPositive grade
        (sharedStrongResponse parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state context.small data) weighted := by
  intro grade
  let weighted := (grades grade).choose
  have actual := (grades grade).choose_spec
  let result := (sameSharedInverse_inserted_tame parameters L compact context.lengthPositive grade).choose_spec.2 context data weighted actual
  exact ⟨result.choose, result.choose_spec.1⟩

end Grad.AnnularHighGenerators
