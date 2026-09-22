import AJD8ActualKnownZeroFunctionalPullback

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.ActualBoundaryPrimitives Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource
open Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.AnnularHighInverseOrbit
open Grad.AnnularCurrentBoundary Grad.AnnularCurrentInverse Grad.AnnularPhysicalSolution Grad.AnnularCurrentSolution

private theorem solution_eq_inverse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (forward : E →L[ℝ] F) (inverse : F →L[ℝ] E)
    (left : inverse.comp forward = ContinuousLinearMap.id ℝ E) (field : E) (source : F)
    (equation : forward field = source) : field = inverse source :=
  (congrArg (fun op : E →L[ℝ] E => op field) left).symm.trans (congrArg inverse equation)

attribute [local instance] Grad.AnnularCrossOrbit.crossDataNormed Grad.AnnularCrossOrbit.crossDataSeminormed
  Grad.AnnularCrossOrbit.crossDataRealInner Grad.AnnularCrossOrbit.crossDataRealNormed Grad.AnnularCrossOrbit.crossDataRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

/-- The actual cross energy response already lies in the original zero-trace space. -/
def crossZeroEnergyResponse : CrossHighData parameters lower →L[ℂ]
    annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive :=
  (crossEnergyResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small).codRestrict
    (annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) (fun datum => by
      have incoming := actualHighGraphEnergySolution_inner parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
        (crossKnownWeighted parameters lower datum) (crossKnownAuxiliary parameters lower datum)
        (0 : HighRadialSourceGraphs parameters lower 0) datum.ofLp.2 (0 : AnnularBoundary)
      change annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
        (crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small datum) = 0
      simpa only [crossEnergyValue, graphDataEnergySolution, CrossHighData.toGraphKnown, map_zero] using incoming)

theorem crossZeroEnergyResponse_val (datum : CrossHighData parameters lower) :
    (crossZeroEnergyResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small datum).val =
      crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small datum := rfl

def crossZeroEnergyOrbit (tau : OrbitParameter) : CrossHighData parameters lower →L[ℂ]
    annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive :=
  (zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive tau).comp
    ((crossZeroEnergyResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small).comp
      (crossDataTranslation parameters lower (-tau)))

theorem crossZeroEnergyOrbit_cancel (tau : OrbitParameter) (datum : CrossHighData parameters lower) :
    zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (-tau)
      (crossZeroEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau datum) =
      crossZeroEnergyResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
        (crossDataTranslation parameters lower (-tau) datum) :=
  (zeroTestTranslationEquivalence lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive tau).symm_apply_apply
    (crossZeroEnergyResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (crossDataTranslation parameters lower (-tau) datum))

/-- Actual physical equation after conjugation, with the exact known functional. -/
theorem crossZeroEnergyOrbit_forward (tau : OrbitParameter) (datum : CrossHighData parameters lower) :
    currentHighZeroFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau
      (crossZeroEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau datum) =
      crossKnownZeroFunctionalOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau datum := by
  apply ContinuousLinearMap.ext
  intro test
  have pullback := currentHighZeroFormOrbit_pullback parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau
    (crossZeroEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau datum) test
  have canceled := congrArg (fun field : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive =>
      currentHighZeroForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field
        (zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (-tau) test))
    (crossZeroEnergyOrbit_cancel parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau datum)
  have literal := currentHighZeroForm_literal parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (crossZeroEnergyResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (crossDataTranslation parameters lower (-tau) datum))
    (zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (-tau) test)
  have equation := congrArg Complex.re (crossEnergyValue_equation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (crossDataTranslation parameters lower (-tau) datum)
    (zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (-tau) test))
  have known := crossKnownZeroFunctionalOrbit_apply parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau datum test
  exact pullback.trans (canceled.trans (literal.trans (equation.trans known.symm)))

/-- The SAME complex energy orbit restricts to the already checked actual real J(tau) applied to F(tau). -/
theorem crossZeroEnergyOrbit_sameInverse (tau : OrbitParameter) :
    (crossZeroEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau).restrictScalars ℝ =
      (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau).comp
        (crossKnownZeroFunctionalOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau) := by
  apply ContinuousLinearMap.ext
  intro datum
  exact solution_eq_inverse
    (currentHighZeroFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau)
    (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)
    (currentHighInverseOrbit_left parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)
    _ _ (crossZeroEnergyOrbit_forward parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau datum)

end Grad.AnnularCrossOrbit
