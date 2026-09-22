import SC4AnnularSubstitution
import SC2GlobalFrameMargin
import AXL11AngularFourier

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 900000

open Set MeasureTheory
open scoped Interval BigOperators

namespace Grad.SourceCollar

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.NonlinearRange Grad.FlatSourceProjection
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation
open Grad.GaugeCoefficients.Physical.Ledger

/-- Physical Fourier evaluation of one original core. -/
def sourceCoreValue {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (point : ClosedDisk) (axialAngle : ℝ) :
    ComplexEuclidean dimension :=
  coreValue field point axialAngle

theorem sourceCoreValue_eq_originalPhysicalEvaluationLift
    {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (point : ClosedDisk) (axialAngle : ℝ) :
    sourceCoreValue field point axialAngle =
      originalPhysicalEvaluationLift parameters
        (GradeCore.ofCoreLinear (grade := 0) field) point axialAngle := by
  rw [originalPhysicalEvaluationLift_eq_tsum]
  unfold sourceCoreValue coreValue
  apply tsum_congr
  intro cell
  rw [axialPhase_eq_character, cellCharacter_coe]
  simp only [GradeCore.toCore_ofCore]

theorem sourceCoreValue_polar_continuous
    {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (radius : ℝ) (bounded : |radius| ≤ 1)
    (axialAngle : ℝ) :
    Continuous (fun polarAngle => sourceCoreValue field
      (polarClosedPoint radius bounded polarAngle) axialAngle) := by
  have pointCurve : Continuous (fun polarAngle : ℝ =>
      Grad.GaugeCoefficients.Radial.rotatedPoint polarAngle
        (axisClosedPoint radius bounded)) := by
    exact Grad.GaugeCoefficients.Radial.continuous_rotatedPoint_joint.comp
      (continuous_id.prodMk continuous_const)
  have physicalContinuous : Continuous (fun point : ClosedDisk =>
      originalPhysicalEvaluationLift parameters
        (GradeCore.ofCoreLinear (grade := 0) field) point axialAngle) := by
    change Continuous (fun point : ClosedDisk =>
      (originalPhysicalClosedJet parameters field).value (point, (axialAngle : CellCircle)))
    exact (originalPhysicalClosedJet parameters field).value.continuous.comp
      (continuous_id.prodMk continuous_const)
  have functionEquality :
      (fun polarAngle => sourceCoreValue field
        (polarClosedPoint radius bounded polarAngle) axialAngle) =
      ((fun point : ClosedDisk => originalPhysicalEvaluationLift parameters
        (GradeCore.ofCoreLinear (grade := 0) field) point axialAngle) ∘
          (fun polarAngle : ℝ => Grad.GaugeCoefficients.Radial.rotatedPoint polarAngle
            (axisClosedPoint radius bounded))) := by
    funext polarAngle
    rw [sourceCoreValue_eq_originalPhysicalEvaluationLift]
    rfl
  rw [functionEquality]
  exact physicalContinuous.comp pointCurve

/-- Physical source slice at fixed axial angle and physical radius. -/
def actualCartesianSourceSlice {parameters : PhaseParameters}
    (source : CartesianSourceCore parameters) (radius : ℝ) (bounded : |radius| ≤ 1)
    (axialAngle : ℝ) : AngularCartesianSource where
  planar polarAngle := sourceCoreValue source.1
    (polarClosedPoint radius bounded polarAngle) axialAngle
  scalarG polarAngle := sourceCoreValue source.2.1
    (polarClosedPoint radius bounded polarAngle) axialAngle 0
  scalarH polarAngle := sourceCoreValue source.2.2
    (polarClosedPoint radius bounded polarAngle) axialAngle 0

/-- Actual BS29 coefficient slice from the literal global frame at the same
physical radius as the source.  No normalized-cap scale enters this identity. -/
def actualPhysicalKappaSlice (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (radius : ℝ) (bounded : |radius| ≤ 1)
    (axialAngle : ℝ) :
    ℝ → Fin 3 → ℂ :=
  fun polarAngle => physicalKappa polarAngle
    (originalPhysicalSignedCofactor parameters L epsilon field axialAngle
      (polarClosedPoint radius bounded polarAngle))

/-- Actual literal BS30 bulk data on one punctured physical polar circle. -/
def actualAnnularBulkSource (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (radius : ℝ) (bounded : |radius| ≤ 1)
    (axialAngle : ℝ)
    (source : CartesianSourceCore parameters) : AnnularBulkSource :=
  cartesianToAnnular radius L
    (actualPhysicalKappaSlice parameters L epsilon field radius bounded axialAngle)
    (actualCartesianSourceSlice source radius bounded axialAngle)

/-- The actual GC17/physical-source instance of the BS30→BS32 identity. -/
theorem actualAnnularBulkSource_inverse (parameters : PhaseParameters)
    (L epsilon : ℝ) (field : ACore parameters 3)
    (radius : ℝ) (bounded : |radius| ≤ 1) (LPositive : 0 < L)
    (axialAngle : ℝ) (source : CartesianSourceCore parameters) :
    annularToCartesian radius L
      (actualPhysicalKappaSlice parameters L epsilon field radius bounded axialAngle)
      (actualAnnularBulkSource parameters L epsilon field radius bounded axialAngle source) =
      actualCartesianSourceSlice source radius bounded axialAngle := by
  exact annularToCartesian_cartesianToAnnular radius L LPositive _ _

/-- Spatial mode zero is exactly the normalized polar-circle mean after
physical Fourier evaluation. -/
theorem sourceAngularAverage_sourceCoreValue
    {parameters : PhaseParameters} (field : ACore parameters 1)
    (radius : ℝ) (bounded : |radius| ≤ 1) (axialAngle : ℝ) :
    sourceAngularAverage (fun polarAngle =>
      sourceCoreValue field (polarClosedPoint radius bounded polarAngle) axialAngle 0) =
      coreValue (angularCore parameters 0 field) (axisClosedPoint radius bounded) axialAngle 0 := by
  let projection : ComplexEuclidean 1 →L[ℂ] ℂ :=
    PiLp.proj 2 (fun _ : Fin 1 => ℂ) 0
  have vectorIntegrable : IntervalIntegrable (fun angle : ℝ =>
      coreValue field
        (Grad.GaugeCoefficients.Radial.rotatedPoint angle (axisClosedPoint radius bounded))
        axialAngle) volume 0 (2 * Real.pi) :=
    (sourceCoreValue_polar_continuous field radius bounded axialAngle).intervalIntegrable _ _
  have identity := congrArg projection
    (Grad.ChartAxisLift.coreValue_angularCore 0 field
      (axisClosedPoint radius bounded) axialAngle)
  simp only [angularCharacter_zero_mode, one_smul] at identity
  have scalarLaw := (projection.restrictScalars ℝ).map_smul
    ((2 * Real.pi)⁻¹) (∫ angle in (0 : ℝ)..2 * Real.pi,
      coreValue field
        (Grad.GaugeCoefficients.Radial.rotatedPoint angle (axisClosedPoint radius bounded))
        axialAngle)
  change projection (((2 * Real.pi)⁻¹ : ℝ) •
      ∫ angle in (0 : ℝ)..2 * Real.pi,
        coreValue field
          (Grad.GaugeCoefficients.Radial.rotatedPoint angle (axisClosedPoint radius bounded))
          axialAngle) =
    ((2 * Real.pi)⁻¹ : ℝ) • projection
      (∫ angle in (0 : ℝ)..2 * Real.pi,
        coreValue field
          (Grad.GaugeCoefficients.Radial.rotatedPoint angle (axisClosedPoint radius bounded))
          axialAngle) at scalarLaw
  rw [scalarLaw, ← projection.intervalIntegral_comp_comm vectorIntegrable] at identity
  change (coreValue (angularCore parameters 0 field) (axisClosedPoint radius bounded)
      axialAngle) 0 =
    ((2 * Real.pi)⁻¹ : ℝ) • ∫ angle in (0 : ℝ)..2 * Real.pi,
      (coreValue field
        (Grad.GaugeCoefficients.Radial.rotatedPoint angle (axisClosedPoint radius bounded))
        axialAngle) 0 at identity
  exact identity.symm

theorem sourceAngularAverage_sourceCoreValue_zero
    {parameters : PhaseParameters} (field : ACore parameters 1)
    (meanZero : angularCore parameters 0 field = 0)
    (radius : ℝ) (bounded : |radius| ≤ 1) (axialAngle : ℝ) :
    sourceAngularAverage (fun polarAngle =>
      sourceCoreValue field (polarClosedPoint radius bounded polarAngle) axialAngle 0) = 0 := by
  rw [sourceAngularAverage_sourceCoreValue, meanZero]
  simp [coreValue]

/-- The two scalar mean constraints of an actual original flat source become
the required mean-zero `F2` and incoming scalar source. -/
theorem actualCartesianSourceSlice_scalar_means
    {parameters : PhaseParameters} (source : CartesianSourceCore parameters)
    (flat : CartesianCoreIsFlat source)
    (radius : ℝ) (bounded : |radius| ≤ 1) (axialAngle : ℝ) :
    sourceAngularAverage (actualCartesianSourceSlice source radius bounded axialAngle).scalarG = 0 ∧
      sourceAngularAverage (actualCartesianSourceSlice source radius bounded axialAngle).scalarH = 0 := by
  constructor
  · exact sourceAngularAverage_sourceCoreValue_zero source.2.1 flat.2.2.2.1
      radius bounded axialAngle
  · exact sourceAngularAverage_sourceCoreValue_zero source.2.2 flat.2.2.2.2.1
      radius bounded axialAngle

end Grad.SourceCollar
