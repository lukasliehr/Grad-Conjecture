import AKBQ8SameScaledNativeGluing
import AKBQ9ActualObservedNativeGauges
import AKBK5SameNativeGlobalForceFields

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.ActualScaledNativeCoefficients
open Grad.ActualCartesianWeakEquations Grad.CartesianStartup Grad.GenericCarriers
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





open Grad.AnnularKernelContinuity
open Grad.AnnularPhysicalReconstruction Grad.AnnularKernelL2 Grad.SourceCollarDivision


open Grad.ActualPuncturedReconstruction Grad.AnnularCurrentEnergy

open Grad.ActualPuncturedFamily Grad.ActualPhysicalField

variable (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (fields : ∀ index, OriginalFiveBlockAmbient parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index))


variable
    (member : ∀ index, fields index ∈ OriginalObservedEquationGraph parameters length compact
      (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
      (originalExhaustionRadius_half length lengthPositive index) lengthPositive widthHalf widthLength state)
    (sameSources : ∀ index, (fields index).ofLp.2 =
      (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0).val.ofLp.1)
    (allGrades : ∀ index grade : ℕ, ∃ weighted : CoupledSpace (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive,
      CoupledInsertedGrade (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index) lengthPositive grade
        (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length
          (originalExhaustionRadius_positive length lengthPositive index)
          ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) weighted)


open Grad.ActualCartesianFlux
open Grad.ActualCartesianDescent Grad.ClosedJets Grad.DiskExtension.Operator Grad.BoundaryTrace Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularGeneralSourceRegularity Grad.ActualSmoothPhysicalField Grad.PuncturedRetainedEnergy
variable (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)


open Grad.PDEBootstrap Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope Grad.Constraints Grad.Constraints.Gauges

/-- The literal SAME full covariant at y=ell Y, before taking its axial cells. -/
def actualScaledCovariantRaw (ell : ℝ) (pair : ℝ×Spatial) : PhysicalValue 3 :=
  actualCartesianCovariantFamilyField parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades (ell • pair.2,pair.1)

include compatible in
theorem actualScaledCovariantRaw_regular (ell : ℝ) (ellPositive : 0 < ell) (ellBounded : ell ≤ 1) :
    StartupOrbitContinuous (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades ell) :=
  scaledNativeFamilyRaw_regular parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive) (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) (fun index => cartesianCovariantRow (originalExhaustionRadius length index) (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index)) (fun index => (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianCovariant) (cartesianCovariantRows_compatible (originalExhaustionRadius length) (originalExhaustionRadius_antitone length lengthPositive) (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (fun first second ordered => (cartesianSourcePolarAndXi_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).1)) ell ellPositive ellBounded

include compatible in
theorem actualScaledCovariantRaw_polar (ell radius : ℝ) (physicalPositive : 0 < ell*radius)
    (radiusNonnegative : 0 ≤ radius) (radiusBounded : |radius| ≤ 1)
    (index : ℕ) (inside : ell*radius ∈ Icc (originalExhaustionRadius length index) 1) (polar axial : ℝ) :
    actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades ell (axial,(Grad.Constraints.polarClosedPoint radius radiusBounded polar).val) =
      cartesianCovariantValue polar ((cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).fullField
        ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (ell*radius,polar,axial)) := by
  have actual := scaledNativeFamilyRaw_polar parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive) (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) (fun index => cartesianCovariantRow (originalExhaustionRadius length index) (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index)) (fun index => (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianCovariant) (cartesianCovariantRows_compatible (originalExhaustionRadius length) (originalExhaustionRadius_antitone length lengthPositive) (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (fun first second ordered => (cartesianSourcePolarAndXi_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).1)) ell radius physicalPositive radiusNonnegative radiusBounded index inside polar axial
  exact actual.trans ((cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).fullField_cartesianCovariant
    ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) _ inside (polar,axial))

include compatible in
/-- Both literal BL32 means for the SAME actual compatible source solution, with every local identity and native gauge discharged. -/
theorem actualScaledCovariantRaw_gaugeMeans {ell : ℝ}
    (admissible : Admissible length parameters.sigma0 parameters.gamma ell)
    (ledger : ActualLedger parameters admissible state.val.val.rho state.val.val.alpha state.val.val.delta
      state.val.val.parameter state.val.val.epsilon state.val.val.field)
    (radius : ℝ) (positive : 0 < radius) (inside : radius < 1) (bounded : |radius| ≤ 1) (cell : ℤ) :
    angularCoefficient (fun polar => polarTangentialComponent polar (planarPartMap
      (angularCoefficient (fun axial => startupRawMatrix (fullGaugeFamily ledger.val.gaugeDeviation)
        (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades ell)
        (axial,(Grad.Constraints.polarClosedPoint radius bounded polar).val)) cell))) 0 = 0 ∧
    angularCoefficient (fun polar => toroidalPartMap
      (angularCoefficient (fun axial => startupRawMatrix (fullGaugeFamily ledger.val.gaugeDeviation)
        (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades ell)
        (axial,(Grad.Constraints.polarClosedPoint radius bounded polar).val)) cell)) 0 = 0 := by
  have physicalPositive : 0 < ell*radius := mul_pos admissible.2.2.2.1 positive
  let index := selectedInnerCollar (originalExhaustionRadius length) (originalExhaustionRadius_tendsto length) (ell*radius) physicalPositive
  have physicalInside : ell*radius ∈ Icc (originalExhaustionRadius length index) 1 :=
    ⟨(selectedInnerCollar_lt (originalExhaustionRadius length) (originalExhaustionRadius_tendsto length) (ell*radius) physicalPositive).le,
      (mul_le_of_le_one_left positive.le (admissible.2.2.2.2.trans (min_le_left _ _))).trans inside.le⟩
  let curves := cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index
  let collarBound := (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num : (1:ℝ)/2 < 1)
  apply scaledRawGauge_cellMeans admissible state.val.val ledger
    (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades ell)
    (actualScaledCovariantRaw_regular parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible ell admissible.2.2.2.1 (admissible.2.2.2.2.trans (min_le_left _ _)))
    radius positive inside bounded (fun angles => curves.fullField collarBound (ell*radius,angles))
    (curves.fullField_continuous_angles collarBound _ physicalInside)
    (actualScaledCovariantRaw_polar parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible ell radius physicalPositive positive.le bounded index physicalInside) cell
  intro kind
  exact actualObservedPolarCurves_gaugeMeans parameters length compact (originalExhaustionRadius length index)
    (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index)
    lengthPositive widthHalf widthLength state
    (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    source flat (fields index) (member index) (sameSources index) (allGrades index) ⟨ell*radius,physicalInside⟩ kind cell

end Grad.ActualScaledNativeCoefficients
