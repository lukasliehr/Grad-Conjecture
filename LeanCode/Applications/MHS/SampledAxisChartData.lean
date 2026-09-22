import PhysicalNormalHessianConsumer
import SampledPhysicalSimilarityRigidity

noncomputable section

open Filter

namespace Grad.MainAssembly.SampledAxisChartData

open Grad.MainTarget
open Grad.MainAssembly.CircleIsometryClassification
open Grad.MainAssembly.PhysicalNormalHessian
open Grad.MainAssembly.PhysicalSimilarityRigidity
open Grad.MainAssembly.NormalHessianSeedBridge
open Grad.MainAssembly.SampledPhysicalSimilarityRigidity
open Grad.GeometryClosure

/-- Construction-facing axis-chart data with the exact integer-resampled
two-harmonic seed angle. -/
def HasSampledAxisChartSeedData (representative : Representative)
    (radius : ℝ) (period : ℕ) (rho alpha delta parameter : ℝ) : Prop :=
  ∃ (pressure : Vec → ℝ) (chart : ℝ → Vec → Vec)
    (coordinatePoint : ℝ → Vec) (potential : ℝ) (a : ℝ → ℝ)
    (tilt : ℝ → Fin 2 → ℝ),
    (∀ point : Reference,
      pressure (representative.position point) = representative.pressure point) ∧
    (∀ time, 0 < a time) ∧
    (∀ time, chart time (coordinatePoint time) = radius • axisRadial time) ∧
    (∀ time, ContDiffAt ℝ 2 pressure (chart time (coordinatePoint time))) ∧
    (∀ time, ContDiffAt ℝ 2 (chart time) (coordinatePoint time)) ∧
    (∀ time, fderiv ℝ pressure (chart time (coordinatePoint time)) = 0) ∧
    (∀ time, (pressure ∘ chart time) =ᶠ[nhds (coordinatePoint time)]
      coordinatePressure potential) ∧
    ∀ time,
      HasAxisDerivative (chart time) (coordinatePoint time) radius time (a time)
        (seedMatrix rho
          (sampledAlphaAngle period alpha delta parameter time))
        (tilt time)

theorem hasPrescribedNormalShape_of_sampledAxisChartSeedData
    (representative : Representative) (radius : ℝ) (period : ℕ)
    (rho alpha delta parameter : ℝ)
    (radiusPositive : 0 < radius) (rhoLower : -1 < rho) (rhoUpper : rho < 1)
    (data : HasSampledAxisChartSeedData representative radius period rho alpha
      delta parameter) :
    HasPrescribedNormalShape representative radius rho
      (sampledAlphaAngle period alpha delta parameter) := by
  rcases data with
    ⟨pressure, chart, coordinatePoint, potential, a, tilt, represents,
      aPositive, chartPoint, pressureSmooth, chartSmooth, critical,
      pullback, axisDerivative⟩
  refine ⟨pressure, represents, ?_⟩
  intro time
  have formula := physical_normal_hessian_formula pressure (chart time)
    (coordinatePoint time) potential radius time (a time)
    (seedMatrix rho (sampledAlphaAngle period alpha delta parameter time))
    (tilt time) radiusPositive.ne' (aPositive time).ne'
    (isUnit_iff_ne_zero.mpr
      (ne_of_gt (seed_det rhoLower rhoUpper
        (sampledAlphaAngle period alpha delta parameter time)).2))
    (chartPoint time) (pressureSmooth time) (chartSmooth time)
    (critical time) (pullback time) (axisDerivative time)
  have exactShape := normalHessian_seed_shape pressure radius time (a time) rho
    (sampledAlphaAngle period alpha delta parameter time) (aPositive time)
    rhoLower rhoUpper formula
  exact ⟨exactShape.1, exactShape.2.2.2⟩

end Grad.MainAssembly.SampledAxisChartData
