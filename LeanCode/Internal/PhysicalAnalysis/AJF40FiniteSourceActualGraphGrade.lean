import AJF35SameSolutionGeneratorApplication
import AJE48FiniteCompleteStrongOrbit

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

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
  (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
  (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact)

/-- For genuine finite prescribed source data, the SAME complete coupled
solution belongs to every literal original inserted graph grade. -/
theorem finiteSharedResponse_insertedGrade
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (support : StrongCutSupport) (finite : StrongSupported parameters lower positive (lowerHalf.trans (by norm_num)) support data)
    (grade : ℕ) :
    ∃ weighted : CoupledSpace lower L positive lengthPositive,
      CoupledInsertedGrade lower L positive lengthPositive grade
        (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) weighted ∧
      ‖weighted‖ ≤ coupledGeneratorGradeConstant grade *
        (‖sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data‖ +
          ‖coupledAxisGenerator lower L positive lengthPositive
            (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) false grade‖ +
          ‖coupledAxisGenerator lower L positive lengthPositive
            (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) true grade‖) :=
  coupled_insertedGrade_of_smoothOrbit lower L positive lengthPositive
    (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
    (fun axis => sharedStrongResponse_axis_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data axis
      (finiteStrongDataOrbit_contDiff parameters lower positive (lowerHalf.trans (by norm_num)) data support finite axis)) grade

end Grad.AnnularHighGenerators
