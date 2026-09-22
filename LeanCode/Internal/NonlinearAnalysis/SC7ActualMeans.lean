import SC6RadialMean
import SC2GlobalFrameContinuity

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Interval BigOperators Topology

namespace Grad.SourceCollar

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.NonlinearRange Grad.FlatSourceProjection Grad.NonlinearProduct
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation
open Grad.GaugeCoefficients.Physical.Ledger

theorem physicalKappa_curve_continuous (matrix : ℝ → Matrix (Fin 3) (Fin 3) ℂ)
    (matrixContinuous : Continuous matrix) :
    Continuous (fun angle => physicalKappa angle (matrix angle)) := by
  apply continuous_pi
  intro coordinate
  fin_cases coordinate <;>
    simp [physicalKappa, matrixPairing, physicalRadialVector,
      physicalTangentialVector, physicalToroidalVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three] <;>
    fun_prop

theorem actualPhysicalKappaSlice_continuous (parameters : PhaseParameters)
    (L epsilon : ℝ) (field : ACore parameters 3)
    (low : originalGradeNorm 4 field + |epsilon| ≤ originalFrameLowRadius parameters L)
    (radius : ℝ) (bounded : |radius| ≤ 1) (axialAngle : ℝ) :
    Continuous (actualPhysicalKappaSlice parameters L epsilon field radius bounded axialAngle) := by
  apply physicalKappa_curve_continuous
  exact originalPhysicalSignedCofactor_polar_continuous_of_low parameters L epsilon field low
    radius bounded axialAngle

theorem polarRadialComponent_curve_continuous {value : ℝ → ComplexEuclidean 2}
    (continuous : Continuous value) :
    Continuous (fun angle => polarRadialComponent angle (value angle)) := by
  unfold polarRadialComponent
  fun_prop

theorem polarTangentialComponent_curve_continuous {value : ℝ → ComplexEuclidean 2}
    (continuous : Continuous value) :
    Continuous (fun angle => polarTangentialComponent angle (value angle)) := by
  unfold polarTangentialComponent
  fun_prop

theorem actualAnnularCorrection_continuous (parameters : PhaseParameters)
    (L epsilon : ℝ) (field : ACore parameters 3)
    (low : originalGradeNorm 4 field + |epsilon| ≤ originalFrameLowRadius parameters L)
    (radius : ℝ) (bounded : |radius| ≤ 1) (axialAngle : ℝ)
    (source : CartesianSourceCore parameters) :
    Continuous (annularCorrection
      (actualPhysicalKappaSlice parameters L epsilon field radius bounded axialAngle)
      (actualAnnularBulkSource parameters L epsilon field radius bounded axialAngle source)) := by
  let kappa := actualPhysicalKappaSlice parameters L epsilon field radius bounded axialAngle
  let sourceSlice := actualCartesianSourceSlice source radius bounded axialAngle
  have planarContinuous : Continuous sourceSlice.planar :=
    sourceCoreValue_polar_continuous source.1 radius bounded axialAngle
  have hVectorContinuous := sourceCoreValue_polar_continuous source.2.2 radius bounded axialAngle
  have hContinuous : Continuous sourceSlice.scalarH :=
    (PiLp.continuous_apply (p := 2) (fun _ : Fin 1 => ℂ) 0).comp hVectorContinuous
  have kappaContinuous : Continuous kappa :=
    actualPhysicalKappaSlice_continuous parameters L epsilon field low radius bounded axialAngle
  have kappa0 : Continuous (fun angle => kappa angle 0) :=
    (continuous_apply 0).comp kappaContinuous
  have kappa1 : Continuous (fun angle => kappa angle 1) :=
    (continuous_apply 1).comp kappaContinuous
  have kappa2 : Continuous (fun angle => kappa angle 2) :=
    (continuous_apply 2).comp kappaContinuous
  have firstContinuous : Continuous (cartesianToAnnular radius L kappa sourceSlice).F1 :=
    polarRadialComponent_curve_continuous planarContinuous
  have zeroContinuous : Continuous (cartesianToAnnular radius L kappa sourceSlice).F0 :=
    polarTangentialComponent_curve_continuous planarContinuous
  have secondContinuous : Continuous (cartesianToAnnular radius L kappa sourceSlice).F2 :=
    hContinuous.div_const _
  change Continuous (fun angle => kappa angle 0 *
      (cartesianToAnnular radius L kappa sourceSlice).F1 angle +
    kappa angle 1 * (cartesianToAnnular radius L kappa sourceSlice).F0 angle -
    kappa angle 2 * (cartesianToAnnular radius L kappa sourceSlice).F2 angle)
  exact (kappa0.mul firstContinuous).add (kappa1.mul zeroContinuous) |>.sub
    (kappa2.mul secondContinuous)

/-- Every required original mean is retained by the actual full `G3`
formula: `F1`, `F2`, and `G3` are mean-free, while `F0` remains unrestricted. -/
theorem actualAnnularBulkSource_means (parameters : PhaseParameters)
    (L epsilon : ℝ) (field : ACore parameters 3)
    (low : originalGradeNorm 4 field + |epsilon| ≤ originalFrameLowRadius parameters L)
    (radius : ℝ) (radiusPositive : 0 < radius) (bounded : |radius| ≤ 1)
    (axialAngle : ℝ) (source : CartesianSourceCore parameters)
    (flat : CartesianCoreIsFlat source) :
    sourceAngularAverage (actualAnnularBulkSource parameters L epsilon field radius bounded
      axialAngle source).F1 = 0 ∧
    sourceAngularAverage (actualAnnularBulkSource parameters L epsilon field radius bounded
      axialAngle source).F2 = 0 ∧
    sourceAngularAverage (actualAnnularBulkSource parameters L epsilon field radius bounded
      axialAngle source).G3 = 0 := by
  let kappa := actualPhysicalKappaSlice parameters L epsilon field radius bounded axialAngle
  let sourceSlice := actualCartesianSourceSlice source radius bounded axialAngle
  have scalarMeans := actualCartesianSourceSlice_scalar_means source flat radius bounded axialAngle
  have gContinuous : Continuous sourceSlice.scalarG := by
    exact (PiLp.continuous_apply (p := 2) (fun _ : Fin 1 => ℂ) 0).comp
      (sourceCoreValue_polar_continuous source.2.1 radius bounded axialAngle)
  have correctionContinuous : Continuous
      (annularCorrection kappa (cartesianToAnnular radius L kappa sourceSlice)) := by
    exact actualAnnularCorrection_continuous parameters L epsilon field low radius bounded
      axialAngle source
  refine ⟨?_, ?_, ?_⟩
  · change sourceAngularAverage (fun angle => polarRadialComponent angle (sourceSlice.planar angle)) = 0
    exact actualCartesianSourceSlice_F1_mean_zero source flat radius bounded axialAngle
  · change sourceAngularAverage (cartesianToAnnular radius L kappa sourceSlice).F2 = 0
    exact cartesianToAnnular_F2_mean_zero radius L kappa sourceSlice scalarMeans.2
  · change sourceAngularAverage (cartesianToAnnular radius L kappa sourceSlice).G3 = 0
    exact cartesianToAnnular_G3_mean_zero radius L radiusPositive kappa sourceSlice
      (gContinuous.intervalIntegrable (0 : ℝ) (2 * Real.pi))
      (correctionContinuous.intervalIntegrable (0 : ℝ) (2 * Real.pi)) scalarMeans.1

end Grad.SourceCollar
