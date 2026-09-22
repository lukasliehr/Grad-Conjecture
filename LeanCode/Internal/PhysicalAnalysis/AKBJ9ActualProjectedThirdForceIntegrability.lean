import AKBJ8NativeMeanFreeOutputIntegrability

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.ActualScalarWeakEquations
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


open Grad.ActualCartesianDescent Grad.ClosedJets Grad.DiskExtension.Operator Grad.BoundaryTrace Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.PuncturedRetainedEnergy
variable (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)

variable (vanishing : SourceHigherVanishing source)
    (graded : ∀ index (_grade : ℕ), CoupledSpace (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive)
    (sameGrade : ∀ index grade, CoupledInsertedGrade (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive grade
      (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) (graded index grade))
    (constants : ℕ → ℝ) (estimate : ∀ index grade, ‖graded index grade‖ ≤ constants grade)
include compatible vanishing sameGrade estimate

open Grad.ActualCartesianFlux

open Grad.ActualNativeCellMoments Grad.ActualCurrentPrimitives

open Grad.ActualForceMoments Grad.CartesianStartup Grad.BoundaryLift Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger

def cartesianSourceForceMatrixRows (index : ℕ) : DivisionRow 3 (originalExhaustionRadius length index) :=
  matrixFluxRows parameters (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field) (forceMatrixFamily_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)) (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive) (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (fun index => cartesianCovariantRow (originalExhaustionRadius length index) (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index)) index

def cartesianSourceForceMatrixCurves (index : ℕ) : SmoothLowPhysicalRow parameters (originalExhaustionRadius length index)
    (originalExhaustionRadius_positive length lengthPositive index) (cartesianSourceForceMatrixRows parameters length compact lengthPositive widthHalf widthLength state small source flat fields index) :=
  matrixFluxCurves parameters (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field) (forceMatrixFamily_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)) (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive) (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (fun index => cartesianCovariantRow (originalExhaustionRadius length index) (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index)) (fun index => (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianCovariant) index

omit vanishing sameGrade estimate in
theorem cartesianSourceForceMatrixRows_compatible (first second : ℕ) (ordered : first ≤ second) :
    originalBulkRestriction 3 (originalExhaustionRadius length second) (originalExhaustionRadius length first)
      (originalExhaustionRadius_antitone length lengthPositive ordered) (cartesianSourceForceMatrixRows parameters length compact lengthPositive widthHalf widthLength state small source flat fields second) =
      cartesianSourceForceMatrixRows parameters length compact lengthPositive widthHalf widthLength state small source flat fields first := by
  apply matrixFluxRows_compatible parameters (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field) (forceMatrixFamily_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)) (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive) (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_antitone length lengthPositive) (fun index => cartesianCovariantRow (originalExhaustionRadius length index) (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index)) _ first second ordered
  exact cartesianCovariantRows_compatible (originalExhaustionRadius length) (originalExhaustionRadius_antitone length lengthPositive)
    (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields)
    (fun first second ordered => (cartesianSourcePolarAndXi_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).1)

def actualCartesianProjectedThirdForceCell (cell : ℤ) (point : SpatialPlane) : ComplexEuclidean 1 :=
  (-2 * (length : ℂ)) • gluedCartesianCellField parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive) (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (originalExhaustionRadius_tendsto length) (fun index => meanFreeRow (originalExhaustionRadius length index) (bulkMatrixUnit (originalExhaustionRadius length index) (0 : Fin 1) (2 : Fin 3) (cartesianSourceForceMatrixRows parameters length compact lengthPositive widthHalf widthLength state small source flat fields index))) (fun index => ((cartesianSourceForceMatrixCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).bulkUnit (0 : Fin 1) 2).meanFree) cell point

private def thirdHilbertProjection (parameters : PhaseParameters) : CellL2 3 →L[ℂ] CellL2 1 :=
  coefficientOperator parameters 0 (Equiv.refl _) (fun _ => matrixUnit (0 : Fin 1) (2 : Fin 3))
    (norm_nonneg _) (fun _ => le_rfl)

/-- The original mean-free third correction is integrable after the entire coefficient convolution; all angular and axial cells are retained. -/
theorem actualCartesianProjectedThirdForceCell_integrable (cell : ℤ) :
    IntegrableOn (actualCartesianProjectedThirdForceCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) openUnitDisk := by
  obtain ⟨C,Cnonnegative,bound⟩ := forceCurve_uniformBound parameters length compact state.val
    state.val.val.rho state.val.val.epsilon state.val.val.field (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small) 2
  have selectedCoherent : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction 1 (originalExhaustionRadius length second) (originalExhaustionRadius length first)
        (originalExhaustionRadius_antitone length lengthPositive ordered)
        (bulkMatrixUnit (originalExhaustionRadius length second) (0 : Fin 1) (2 : Fin 3) (cartesianSourceForceMatrixRows parameters length compact lengthPositive widthHalf widthLength state small source flat fields second)) =
      bulkMatrixUnit (originalExhaustionRadius length first) (0 : Fin 1) (2 : Fin 3) (cartesianSourceForceMatrixRows parameters length compact lengthPositive widthHalf widthLength state small source flat fields first) := by
    intro first second ordered
    rw [bulkMatrixUnit_restriction,cartesianSourceForceMatrixRows_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered]
  obtain ⟨weighted,unweighted,weightedSame,unweightedSame,integrable⟩ := actualCartesianFamily_meanFreeOutputMoments parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades
    vanishing graded sameGrade constants estimate
    (fun index => bulkMatrixUnit (originalExhaustionRadius length index) (0 : Fin 1) (2 : Fin 3) (cartesianSourceForceMatrixRows parameters length compact lengthPositive widthHalf widthLength state small source flat fields index))
    (fun index => (cartesianSourceForceMatrixCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).bulkUnit (0 : Fin 1) 2)
    selectedCoherent (‖thirdHilbertProjection parameters‖ * C) (mul_nonneg (norm_nonneg _) Cnonnegative)
    (fun index radius => by
      change ‖thirdHilbertProjection parameters ((cartesianSourceForceMatrixCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).curve 2 radius)‖ ≤ _
      have matrixBound := bound (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) _
        (actualCartesianSevenCurves parameters length compact (originalExhaustionRadius length index)
          (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index)
          lengthPositive widthHalf widthLength state
          (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
          (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small) source flat (fields index) (member index) (sameSources index) (allGrades index)) radius
      exact ((thirdHilbertProjection parameters).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_left matrixBound (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm))
  exact MeasureTheory.Integrable.bdd_smul (integrable cell) ‖(-2 * (length : ℂ))‖
    aestronglyMeasurable_const (Eventually.of_forall (fun _ => le_rfl))

end Grad.ActualScalarWeakEquations
