import AIC7DiskScalarMultiplication

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace Grad.InteriorLocalization
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.CircularHighWeak

/-- Actual ordinary-area disk pairing, also for tests not supported in the disk. -/
def diskIntegral (field : DiskL2 1) (vector : PhysicalValue 1) (test : Spatial → ℝ) : ℂ :=
  ∫ point in openUnitDisk, test point • inner ℂ vector (field point)

theorem diskIntegral_integrable (field : DiskL2 1) (vector : PhysicalValue 1)
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun point => test point • inner ℂ vector (field point)) (volume.restrict openUnitDisk) := by
  apply (Grad.WeakTesting.pairing_integrable 1 openUnitDisk 0 vector test
    (smooth.continuous.memLp_of_hasCompactSupport compact) (apDiskInjection 1 field)).congr
  filter_upwards [apDiskInjection_ae field] with point injection
  rw [injection, cellSingle_apply, if_pos rfl]

/-- Adjoint cutoff identity after integration against an arbitrary L2 field.
Only smooth compact test functions are differentiated. -/
theorem cutoff_integral_identity (field : DiskL2 1) (vector : PhysicalValue 1)
    (direction : Fin 2) (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (_compact : HasCompactSupport test) :
    diskIntegral field vector (fun point => interiorCutoff.toFun point * secondTestDerivative direction test point) =
      diskIntegral field vector (secondTestDerivative direction (fun point => interiorCutoff.toFun point * test point)) -
        2 * diskIntegral field vector (firstTestDerivative direction
          (fun point => firstTestDerivative direction interiorCutoff.toFun point * test point)) +
        diskIntegral field vector (fun point => secondTestDerivative direction interiorCutoff.toFun point * test point) := by
  let first := secondTestDerivative direction (fun point => interiorCutoff.toFun point * test point)
  let second := firstTestDerivative direction
    (fun point => firstTestDerivative direction interiorCutoff.toFun point * test point)
  let third := fun point => secondTestDerivative direction interiorCutoff.toFun point * test point
  have firstIntegrable := diskIntegral_integrable field vector first
    (secondTestDerivative_smooth direction _ (interiorCutoff.smooth.mul smooth))
    (secondTestDerivative_compact direction _ (interiorCutoff.compact.mul_right))
  have secondIntegrable := diskIntegral_integrable field vector second
    (firstTestDerivative_smooth direction _ ((firstTestDerivative_smooth direction _ interiorCutoff.smooth).mul smooth))
    (firstTestDerivative_compact direction _ ((firstTestDerivative_compact direction _ interiorCutoff.compact).mul_right))
  have thirdIntegrable := diskIntegral_integrable field vector third
    ((secondTestDerivative_smooth direction _ interiorCutoff.smooth).mul smooth)
    ((secondTestDerivative_compact direction _ interiorCutoff.compact).mul_right)
  have identity (point : Spatial) : interiorCutoff.toFun point * secondTestDerivative direction test point =
      first point - 2 * second point + third point :=
    (cutoff_test_identity direction interiorCutoff.toFun test interiorCutoff.smooth smooth point).symm
  change (∫ point in openUnitDisk,
    (interiorCutoff.toFun point * secondTestDerivative direction test point) • inner ℂ vector (field point)) = _
  calc
    _ = ∫ point in openUnitDisk,
        (first point • inner ℂ vector (field point) -
          (2 : ℝ) • (second point • inner ℂ vector (field point))) +
          third point • inner ℂ vector (field point) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun point => by
        dsimp only
        rw [identity point, add_smul, sub_smul, mul_smul])
    _ = (∫ point in openUnitDisk, first point • inner ℂ vector (field point) -
          (2 : ℝ) • (second point • inner ℂ vector (field point))) +
        ∫ point in openUnitDisk, third point • inner ℂ vector (field point) :=
      integral_add (firstIntegrable.sub (secondIntegrable.smul (2 : ℝ))) thirdIntegrable
    _ = ((∫ point in openUnitDisk, first point • inner ℂ vector (field point)) -
        ∫ point in openUnitDisk, (2 : ℝ) • (second point • inner ℂ vector (field point))) +
        ∫ point in openUnitDisk, third point • inner ℂ vector (field point) :=
      congrArg (fun value : ℂ => value + _) (integral_sub firstIntegrable (secondIntegrable.smul (2 : ℝ)))
    _ = _ := by
      rw [integral_smul]
      rfl

end Grad.InteriorLocalization
