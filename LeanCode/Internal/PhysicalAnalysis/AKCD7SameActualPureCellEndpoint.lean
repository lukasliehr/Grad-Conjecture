import AKCD6SameNativeCovariantGlobalEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ActualPuncturedFamily
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularStrongOrbit
open Grad.AnnularForwardTraces Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularRestriction
open Grad.AnnularExhaustionEstimate Grad.AnnularWeakExhaustion Grad.AnnularFullSource
open Grad.AnnularHighGenerators Grad.AnnularCrossOrbit Grad.ActualAnnularExhaustion
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.SourceCollarFullSource Grad.ExhaustionSourceAllocation
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  sourceRadialRealInner sourceGraphRealInner sourceKnownGraphRealInner
  weakRetainedRealInner weakSourcesRealInner weakFiveRealInner

attribute [local instance] weakWeightedRetainedRealInner
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




open Grad.FinitePhysicalJetLift Grad.ActualSmoothPhysicalField Grad.ActualNativeCellMoments
open Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.ClosedJets Grad.SourceBoundaryTrace
open MeasureTheory
open scoped ENNReal BigOperators

variable {parameters : PhaseParameters} {length compact : ℝ} {lengthPositive : 0 < length}
    {widthHalf : parameters.gamma ≤ 1 / 2} {widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)}
    {state : RetainedInverseState parameters length compact}
    {small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact}
    {source : SmoothQuotient parameters} {flat : IsFlat source}

open Grad.ActualPhysicalField Grad.ActualCartesianFlux Grad.ActualPuncturedReconstruction
open Grad.PuncturedRetainedEnergy Grad.AnnularPhysicalReconstruction

open Grad.CartesianStartup Grad.ActualCartesianDescent

/-- Pure-cell endpoint at every grade for the SAME actual native covariant.
The original full signed-cell fields and width are retained. -/
theorem nativeCovariant_allCellEndpoint
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (small12 : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 12 ≤ 1)
    (payment : ℕ → ℝ) (nonnegative : ∀ grade, 0≤payment grade)
    (bound : ∀ index grade, family.nativeNorm index grade ≤ payment grade)
    (basePayment : ℝ) (baseNonnegative : 0≤basePayment) (baseBound : ∀ index, family.nativeNorm index 0 ≤ basePayment) :
    ∃ moments : StartupAllMoments 3,
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        moments.field point cell = cartesianWeight parameters cell point •
          actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat family.limit
            (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
            (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) cell point) ∧
      ∀ grade, ‖moments.moment grade‖ ≤ Real.sqrt (2*Real.pi)*nativeCovariantEndpointConstant parameters length compact grade *
        (payment grade+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+12)*basePayment) := by
  let cost (grade : ℕ) := nativeCovariantEndpointConstant parameters length compact grade *
    (payment grade+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+12)*basePayment)
  have costNonnegative (grade : ℕ) : 0≤cost grade := mul_nonneg
    (nativeCovariantEndpointConstant_nonnegative parameters length compact lengthPositive grade)
    (add_nonneg (nonnegative grade) (mul_nonneg (physicalBudget_nonnegative _ _ _ _ _) baseNonnegative))
  have energy (grade : ℕ) := nativeCovariant_globalEnergy family small12 grade (payment grade) (basePayment)
    (nonnegative grade) baseNonnegative (fun index => bound index grade) baseBound
  have finite (grade : ℕ) :
      (∫⁻ radius in Ioc (0:ℝ) 1, ENNReal.ofReal
        (‖gluedWeightedFamilyCurve parameters (originalExhaustionRadius length)
          (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_tendsto length)
          (nativeCovariantRows family) (nativeCovariantCurves family) grade radius‖^2)) < ⊤ :=
    (energy grade).trans_lt ENNReal.ofReal_lt_top
  let moments := sameNativeAllCellMoments parameters (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
    (nativeCovariantRows family) (nativeCovariantCurves family) (nativeCovariantRows_compatible family) finite
  refine ⟨moments,?_,?_⟩
  · exact sameNativeAllCellMoments_same parameters (originalExhaustionRadius length)
      (originalExhaustionRadius_positive length lengthPositive)
      (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
      (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
      (nativeCovariantRows family) (nativeCovariantCurves family) (nativeCovariantRows_compatible family) finite
  · intro grade
    have squared := sameNativeCellField_higherEnergy parameters (originalExhaustionRadius length)
      (originalExhaustionRadius_positive length lengthPositive)
      (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
      (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
      (nativeCovariantRows family) (nativeCovariantCurves family) (nativeCovariantRows_compatible family)
      grade grade (le_refl _) (finite grade) (cost grade) (energy grade)
    have realEnergy := ENNReal.toReal_mono ENNReal.ofReal_ne_top squared
    have square : ‖moments.moment grade‖^2 ≤ (2*Real.pi)*(cost grade)^2 := by
      simpa only [moments,sameNativeAllCellMoments,ENNReal.toReal_ofReal (sq_nonneg _),ENNReal.toReal_ofReal (by positivity : 0≤(2*Real.pi)*(cost grade)^2)] using realEnergy
    have estimate : ‖moments.moment grade‖ ≤ Real.sqrt (2*Real.pi)*cost grade := by
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (costNonnegative grade))).mp
      rw [mul_pow,Real.sq_sqrt (by positivity : 0≤2*Real.pi)]
      exact square
    exact estimate.trans_eq (by dsimp [cost]; ring)

end Grad.OriginalCartesianTameEstimate
