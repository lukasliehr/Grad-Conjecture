import AKDW3OriginalUnitGaugeFourierMeans
import AKBT6ActualNativeCurrentRecovery
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.ActualScaledNativeCoefficients
open Grad.GaugeCoefficients.Physical.Allocation Grad.ActualGaugeSigmaPrimitives
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

include compatible in
/-- Both literal BL32 means for the SAME actual compatible source solution, with every local identity and native gauge discharged. -/
theorem actualOriginalUnitCovariantRaw_gaugeMeans
    (gauge : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3)
    (sameGauge : ∀ grade angle point, familyMatrix (fullGaugeFamily gauge) grade angle point =
      originalPhysicalGaugeMatrix parameters length state.val.val.rho state.val.val.alpha state.val.val.delta
        state.val.val.parameter state.val.val.epsilon state.val.val.field angle point)
    (radius : ℝ) (positive : 0 < radius) (inside : radius < 1) (bounded : |radius| ≤ 1) (cell : ℤ) :
    angularCoefficient (fun polar => polarTangentialComponent polar (planarPartMap
      (angularCoefficient (fun axial => startupRawMatrix (fullGaugeFamily gauge)
        (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades 1)
        (axial,(Grad.Constraints.polarClosedPoint radius bounded polar).val)) cell))) 0 = 0 ∧
    angularCoefficient (fun polar => toroidalPartMap
      (angularCoefficient (fun axial => startupRawMatrix (fullGaugeFamily gauge)
        (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades 1)
        (axial,(Grad.Constraints.polarClosedPoint radius bounded polar).val)) cell)) 0 = 0 := by
  let index := selectedInnerCollar (originalExhaustionRadius length) (originalExhaustionRadius_tendsto length) radius positive
  have physicalInside : radius ∈ Icc (originalExhaustionRadius length index) 1 :=
    ⟨(selectedInnerCollar_lt (originalExhaustionRadius length) (originalExhaustionRadius_tendsto length) radius positive).le,
      inside.le⟩
  let curves := cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index
  let collarBound := (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num : (1:ℝ)/2 < 1)
  apply originalUnitRawGauge_cellMeans state.val.val gauge sameGauge
    (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades 1)
    (actualScaledCovariantRaw_regular parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible 1 zero_lt_one le_rfl)
    radius positive inside bounded (fun angles => curves.fullField collarBound (radius,angles))
    (curves.fullField_continuous_angles collarBound _ physicalInside)
    (by
      intro polar axial
      simpa only [one_mul] using actualScaledCovariantRaw_polar parameters length compact lengthPositive widthHalf widthLength
        state small source flat fields member sameSources allGrades compatible 1 radius (by simpa using positive)
        positive.le bounded index (by simpa using physicalInside) polar axial) cell
  intro kind
  exact actualObservedPolarCurves_gaugeMeans parameters length compact (originalExhaustionRadius length index)
    (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index)
    lengthPositive widthHalf widthLength state
    (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    source flat (fields index) (member index) (sameSources index) (allGrades index) ⟨radius,physicalInside⟩ kind cell

end Grad.ActualScaledNativeCoefficients
