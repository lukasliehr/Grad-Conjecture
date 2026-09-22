import AKBJ10LiteralProjectedThirdForce

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
open Grad.AnnularGeneralSourceRegularity Grad.ActualSmoothPhysicalField Grad.PuncturedRetainedEnergy
variable (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)

open Grad.ActualForceMoments Grad.ActualCartesianWeakEquations Grad.SourceCollar Grad.GaugeCoefficients.Physical.Ledger
include compatible


omit compatible in
/-- Opaque equality of the existing canonical matrix-output providers. -/
theorem sourceProjectedThirdForce_fullField_same (index : ℕ) :
    (((cartesianSourceForceMatrixCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).bulkUnit (0 : Fin 1) 2).meanFree).fullField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) = (((sameForceMatrixCurves parameters length state.val.val.rho state.val.val.epsilon state.val.val.field (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small) (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index)).bulkUnit (0 : Fin 1) 2).meanFree).fullField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) := by
  rfl

theorem actualProjectedThirdForceCell_full (cell : ℤ) (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc (originalExhaustionRadius length index) 1) (polar : ℝ) :
    actualCartesianProjectedThirdForceCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell (polarPlane (radius,polar)) =
      angularCoefficient (fun axial => (-2 * (length : ℂ)) • (((cartesianSourceForceMatrixCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).bulkUnit (0 : Fin 1) 2).meanFree).fullField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (radius,polar,axial)) cell := by
  have coherent : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction 1 (originalExhaustionRadius length second) (originalExhaustionRadius length first)
        (originalExhaustionRadius_antitone length lengthPositive ordered) ((fun index => meanFreeRow (originalExhaustionRadius length index) (bulkMatrixUnit (originalExhaustionRadius length index) (0 : Fin 1) (2 : Fin 3) (cartesianSourceForceMatrixRows parameters length compact lengthPositive widthHalf widthLength state small source flat fields index))) second) = (fun index => meanFreeRow (originalExhaustionRadius length index) (bulkMatrixUnit (originalExhaustionRadius length index) (0 : Fin 1) (2 : Fin 3) (cartesianSourceForceMatrixRows parameters length compact lengthPositive widthHalf widthLength state small source flat fields index))) first := by
    intro first second ordered
    dsimp only
    rw [originalBulkRestriction_meanFree,bulkMatrixUnit_restriction,
      cartesianSourceForceMatrixRows_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered]
  have actual := gluedCartesianCellField_same parameters (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
    (fun index => meanFreeRow (originalExhaustionRadius length index) (bulkMatrixUnit (originalExhaustionRadius length index) (0 : Fin 1) (2 : Fin 3) (cartesianSourceForceMatrixRows parameters length compact lengthPositive widthHalf widthLength state small source flat fields index))) (fun index => ((cartesianSourceForceMatrixCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).bulkUnit (0 : Fin 1) 2).meanFree) coherent cell index (polarPlane (radius,polar))
    (by simpa only [polarPlane_norm,abs_of_pos ((originalExhaustionRadius_positive length lengthPositive index).trans_le inside.1)] using inside)
  unfold actualCartesianProjectedThirdForceCell
  rw [actual]
  have localActual := (((cartesianSourceForceMatrixCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).bulkUnit (0 : Fin 1) 2).meanFree).cartesianCellField_actual ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) cell radius inside polar
  rw [polarPlane_originalParametrization] at localActual
  rw [localActual]
  exact (angularCoefficient_smul_continuous (-2 * (length : ℂ))
    (fun axial => (((cartesianSourceForceMatrixCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).bulkUnit (0 : Fin 1) 2).meanFree).fullField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (radius,polar,axial)) cell).symm

/-- Scalar Fourier identity for the literal original mean-free third force correction, retaining its sign and original length. -/
theorem actualProjectedThirdForceCell_literal (cell : ℤ) (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc (originalExhaustionRadius length index) 1) (polar : ℝ) :
    (actualCartesianProjectedThirdForceCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell (polarPlane (radius,polar))) 0 =
      angularCoefficient (fun axial => (length : ℂ) * removePolarMean (fun query =>
        matrixPairing ((-2 : ℂ) • physicalToroidalVector)
          (rotatedPhysicalFrameMatrix parameters 1 1 state.val.val.epsilon state.val.val.field query.2
            (polarClosedPoint radius query.1 ((originalExhaustionRadius_positive length lengthPositive index).le.trans inside.1) inside.2) * Matrix.diagonal ![1,1,(length : ℂ)⁻¹]).transpose
          (((cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).physicalUFromPolar parameters length state.val.val.rho state.val.val.epsilon state.val.val.field (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
            (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))).fullField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (radius,query))) (polar,axial)) cell := by
  rw [actualProjectedThirdForceCell_full parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell index radius inside polar]
  have continuousField : Continuous (fun axial => (-2 * (length : ℂ)) • (((cartesianSourceForceMatrixCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).bulkUnit (0 : Fin 1) 2).meanFree).fullField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (radius,polar,axial)) :=
    ((((cartesianSourceForceMatrixCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).bulkUnit (0 : Fin 1) 2).meanFree).fullField_continuous_angles ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) radius inside).comp
      (continuous_const.prodMk continuous_id) |>.const_smul (-2 * (length : ℂ))
  rw [angularCoefficient_component _ continuousField 0 cell]
  congr 1
  funext axial
  rw [PiLp.smul_apply,smul_eq_mul]
  rw [sourceProjectedThirdForce_fullField_same parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index]
  exact sameProjectedThirdForce_fullField parameters length state.val.val.rho state.val.val.epsilon state.val.val.field (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index) radius inside (polar,axial)

end Grad.ActualScalarWeakEquations
