import AKBK11ActualPlanarForceCellFidelity
import AKBK12OriginalForceAngularContinuity
import AKBK14OriginalPlanarSourceCells

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.ActualCartesianWeakEquations
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

open Grad.PhysicalFamily Grad.PDEBootstrap Grad.Constraints
open Grad.ActualScalarWeakEquations Grad.ActualForceMoments Grad.ActualCartesianEquations Grad.Constraints.Gauges

include compatible

/-- Every genuine observed annular equation gives the literal projected
Cartesian equation on the SAME global native axial cells. -/
theorem actualCartesianPlanarForceCell_projected (cell : ℤ) (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Ioo (originalExhaustionRadius length index) 1) (polar : ℝ) :
    actualCartesianPlanarForceCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell (polarPlane (radius,polar)) -
      angularCoefficient (fun angle => polarRadialComponent angle
        (actualCartesianPlanarForceCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell (polarPlane (radius,angle)))) 0 • polarRadialVector polar =
    originalCoreCell parameters (cartesianSourceVector source) cell (polarPlane (radius,polar)) -
      angularCoefficient (fun angle => polarRadialComponent angle
        (originalCoreCell parameters (cartesianSourceVector source) cell (polarPlane (radius,angle)))) 0 • polarRadialVector polar := by
  have radiusPositive : 0 < radius := (originalExhaustionRadius_positive length lengthPositive index).trans inside.1
  have original := actualObserved_originalForceAndThird parameters length compact
    (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
    (originalExhaustionRadius_half length lengthPositive index) lengthPositive widthHalf widthLength state
    (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    source flat (fields index) (member index) (sameSources index) (allGrades index)
    (actualCartesianSevenCurves parameters length compact (originalExhaustionRadius length index)
      (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index)
      lengthPositive widthHalf widthLength state
      (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
      (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
      source flat (fields index) (member index) (sameSources index) (allGrades index)) radius inside
  have equation : ∀ angles,
      cartesianRadialMeanFree (actualCartesianRawForceFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index radius ⟨inside.1.le,inside.2.le⟩) angles =
      cartesianRadialMeanFree (literalCartesianPlanarSource parameters source radius radiusPositive.le inside.2.le) angles := by
    intro angles
    exact (original angles).1
  have selected := originalProjectedEquation_axialCell
    (actualCartesianRawForceFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index radius ⟨inside.1.le,inside.2.le⟩)
    (literalCartesianPlanarSource parameters source radius radiusPositive.le inside.2.le)
    (actualCartesianRawForceFamily_continuous parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible index radius inside)
    (literalCartesianPlanarSource_continuous parameters source radius radiusPositive.le inside.2.le)
    equation cell polar
  simp_rw [actualCartesianPlanarForceCell_original parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell index radius inside,
    literalCartesianPlanarSource_axialCell] at selected
  exact selected

end Grad.ActualCartesianWeakEquations
