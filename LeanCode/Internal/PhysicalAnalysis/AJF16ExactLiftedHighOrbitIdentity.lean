import AJF15SameLiftedHighSolverOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularHighInverseOrbit Grad.AnnularCurrentInverse Grad.AnnularCurrentEnergy
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit Grad.AnnularReconstruction Grad.CartesianState
open Grad.AnnularStrongOrbit Grad.AnnularUniformBoundary Grad.AnnularCurrentSolution

section Algebra
variable {W V D : Type*}
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem liftedAlgebraPullback (inclusion : V →L[ℝ] W) (energy : W →L[ℝ] W)
    (tests : V →L[ℝ] V) (reverse : D →L[ℝ] D) (lift : D →L[ℝ] W)
    (inverse orbitInverse : (V →L[ℝ] ℝ) →L[ℝ] V)
    (form orbitForm : W →L[ℝ] V →L[ℝ] ℝ)
    (inverseActual : ∀ source, orbitInverse source = tests (inverse (source.comp tests)))
    (inclusionActual : ∀ value, inclusion (tests value) = energy (inclusion value))
    (liftActual : ∀ datum, energy (lift (reverse datum)) = lift datum)
    (formActual : ∀ datum test, orbitForm (lift datum) (tests test) = form (lift (reverse datum)) test)
    (source : V →L[ℝ] ℝ) (datum : D) :
    lift datum + inclusion (orbitInverse (source - orbitForm (lift datum))) =
      energy (lift (reverse datum) + inclusion (inverse (source.comp tests - form (lift (reverse datum))))) := by
  have residual : (source - orbitForm (lift datum)).comp tests = source.comp tests - form (lift (reverse datum)) := by
    apply ContinuousLinearMap.ext
    intro test
    change source (tests test) - orbitForm (lift datum) (tests test) = source (tests test) - form (lift (reverse datum)) test
    rw [formActual]
  rw [inverseActual, inclusionActual, residual, map_add, liftActual]

end Algebra

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
  (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
  (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

/-- Exact covariance of the full, nonzero-incoming AEL solution. This
identifies the smooth operator formula with the SAME actual physical solver,
without assuming a translated coefficient state or a new inverse. -/
theorem fullHighEnergySolverOrbit_pullback (tau : OrbitParameter)
    (source : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ)
    (datum : AnnularBoundary) :
    fullHighEnergySolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau source datum =
      energyTranslation lower L positive tau
        (currentHighLiftedSolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
          (source.comp ((zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive tau).restrictScalars ℝ))
          (physicalIncomingNormalize (highIncomingTranslation (-tau) datum))) := by
  have liftActual (boundary : AnnularBoundary) :
      energyTranslation lower L positive tau
        (physicalIncomingLift lower L positive lowerHalf lengthPositive (highIncomingTranslation (-tau) boundary)) =
      physicalIncomingLift lower L positive lowerHalf lengthPositive boundary := by
    exact (physicalIncomingLift_translation lower L positive lowerHalf lengthPositive tau
      (highIncomingTranslation (-tau) boundary)).symm.trans
      (congrArg (physicalIncomingLift lower L positive lowerHalf lengthPositive)
        (highIncomingTranslation_inverse tau boundary))
  have formActual (boundary : AnnularBoundary)
      (test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
      liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau
        (physicalIncomingLift lower L positive lowerHalf lengthPositive boundary)
        (zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive tau test) =
      currentHighTestFunctional parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
        (physicalIncomingLift lower L positive lowerHalf lengthPositive (highIncomingTranslation (-tau) boundary)) test := by
    have pulled := liftedTestFunctionalOrbit_pullback parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau
      (physicalIncomingLift lower L positive lowerHalf lengthPositive boundary)
      (zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive tau test)
    have sameField := (physicalIncomingLift_translation lower L positive lowerHalf lengthPositive (-tau) boundary).symm
    have sameTest := zeroTestTranslation_inverse lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (-tau) test
    simp only [neg_neg] at sameTest
    let form : annularEnergySpace lower L positive →
        annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive → ℝ :=
      fun value point => currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state value point.val
    have congruent := congrArg₂ form sameField sameTest
    exact pulled.trans congruent
  apply (fullHighEnergySolverOrbit_formula parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau source datum).trans
  exact liftedAlgebraPullback
    (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)
    ((energyTranslation lower L positive tau).restrictScalars ℝ)
    ((zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive tau).restrictScalars ℝ)
    ((highIncomingTranslation (-tau)).restrictScalars ℝ)
    ((physicalIncomingLift lower L positive lowerHalf lengthPositive).restrictScalars ℝ)
    (currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)
    (formTestRestriction (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)
      (currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state))
    (liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau)
    (currentHighInverseOrbit_apply parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)
    (zeroTestTranslation_value lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive tau)
    liftActual formActual source datum

end Grad.AnnularHighGenerators
