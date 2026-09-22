import ANJ7LiteralBoundaryData

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.InhomogeneousHighRobin
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.OrdinaryDiskCalculus Grad.ActualSmoothPDE Grad.NonlinearDivision Grad.CircularNormalLift
open Grad.GaugeCoefficients.Physical.RadialLedger
local instance (priority := 2000) weakSolveUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade

private theorem diskPairing_integrable (vector : PhysicalValue 1)
    (test : Grad.PDEBootstrap.Spatial → ℝ) (membership : MemLp test 2 (volume.restrict openUnitDisk))
    (field : DiskL2 1) :
    Integrable (fun point => test point • inner ℂ vector (field point)) (volume.restrict openUnitDisk) := by
  have integrable := Grad.WeakTesting.pairing_integrable 1 openUnitDisk 0 vector test membership (apDiskInjection 1 field)
  apply integrable.congr
  filter_upwards [apDiskInjection_ae field] with point literal
  rw [literal]
  rfl

def diskLaplacianPairing (vector : PhysicalValue 1) (test : Grad.PDEBootstrap.Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) : DiskL2 1 →L[ℂ] ℂ :=
  apDiskDerivativePairing 1 0 vector test smooth compact 2 (fun _ => 0) +
    apDiskDerivativePairing 1 0 vector test smooth compact 2 (fun _ => 1)

theorem diskLaplacianPairing_literal (vector : PhysicalValue 1) (test : Grad.PDEBootstrap.Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) (field : DiskL2 1) :
    diskLaplacianPairing vector test smooth compact field =
      ∫ point in openUnitDisk, testLaplacian test point • inner ℂ vector (field point) := by
  change apDiskDerivativePairing 1 0 vector test smooth compact 2 (fun _ => 0) field +
    apDiskDerivativePairing 1 0 vector test smooth compact 2 (fun _ => 1) field = _
  rw [apDiskDerivativePairing_literal, apDiskDerivativePairing_literal]
  unfold testLaplacian
  simp only [Pi.add_apply, add_smul]
  exact (integral_add
    (diskPairing_integrable vector _ (Grad.WeakTesting.orderedTestDerivative_memLp openUnitDisk 2 (fun _ => 0) test smooth compact) field)
    (diskPairing_integrable vector _ (Grad.WeakTesting.orderedTestDerivative_memLp openUnitDisk 2 (fun _ => 1) test smooth compact) field)).symm

/-- The completed Cartesian operator retains its actual distributional
meaning against every ordinary compact smooth test. -/
theorem unitCartesianLaplacian_weak (grade : ℕ) (field : unitDiskSobolev (grade + 2)) :
    HasDiskWeakLaplacian (unitDiskBulk (grade + 2) field)
      (unitDiskBulk grade (unitCartesianLaplacian grade field)) := by
  intro vector test smooth compact supported
  let pairing := apDiskPairing 1 0 vector test smooth compact
  let derivative := diskLaplacianPairing vector test smooth compact
  have completed : pairing (unitDiskBulk grade (unitCartesianLaplacian grade field)) =
      derivative (unitDiskBulk (grade + 2) field) := by
    apply isClosed_property (unitDiskCoreInto_denseRange (grade + 2))
      (isClosed_eq (pairing.continuous.comp
        ((unitDiskBulk grade).continuous.comp (unitCartesianLaplacian grade).continuous))
        (derivative.continuous.comp (unitDiskBulk (grade + 2)).continuous)) _ field
    intro core
    have first := congrArg pairing (unitCartesianLaplacian_core_bulk grade core)
    have second := (apDiskPairing_literal vector test smooth compact (closedL2Core (laplacianJet core))).trans
      ((closedL2Core_weakLaplacian core vector test smooth compact supported).trans
        (diskLaplacianPairing_literal vector test smooth compact (closedL2Core core)).symm)
    exact first.trans (second.trans (congrArg derivative (unitDiskBulk_core (grade + 2) core)).symm)
  exact (apDiskPairing_literal vector test smooth compact _).symm.trans
    (completed.trans (diskLaplacianPairing_literal vector test smooth compact _))

private theorem scalar_rearrange {E : Type*} [AddCommGroup E] (first laplacian source : E)
    (equation : first - laplacian = source) : laplacian = first - source := by
  have equal := congrArg (fun value => value + laplacian) equation
  simp only [sub_add_cancel] at equal
  rw [equal]
  abel

/-- The completed nonzero-Robin construction solves the literal full-disk
weak scalar equation; its source is not restricted to smooth representatives. -/
theorem inhomogeneousCompletedInverse_weak (grade : ℕ) (parameters : PhaseParameters) (parameter : ℝ)
    (source : unitDiskSobolev grade) (sourceHigh : unitDiskBulk grade source ∈ highDiskL2)
    (boundary : normalBoundaryGrade (grade + 2))
    (boundaryHigh : ∀ mode ∈ Grad.Constraints.lowAngularModes,
      normalBoundaryCoefficient (grade + 2) boundary mode = 0) :
    HasDiskWeakLaplacian
      (unitDiskBulk (grade + 2) (inhomogeneousCompletedInverse grade parameters parameter (source, boundary)))
      (((parameter ^ 2 : ℝ) : ℂ) • diskB
        (unitDiskBulk (grade + 2) (inhomogeneousCompletedInverse grade parameters parameter (source, boundary))) -
          unitDiskBulk grade source) := by
  let solution := inhomogeneousCompletedInverse grade parameters parameter (source, boundary)
  have equation := (unitScalarOperator_bulk grade parameter solution).symm.trans
    (congrArg (unitDiskBulk grade)
      (inhomogeneousCompletedInverse_scalar grade parameters parameter source sourceHigh boundary boundaryHigh))
  have laplacian := scalar_rearrange _ _ _ equation
  exact (congrArg (HasDiskWeakLaplacian (unitDiskBulk (grade + 2) solution)) laplacian).mp
    (unitCartesianLaplacian_weak grade solution)

end Grad.InhomogeneousHighRobin
