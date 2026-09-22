import PhysicalNormalHessian

noncomputable section

open Filter

namespace Grad.MainAssembly.PhysicalNormalHessian.Consumer

open Grad.MainTarget
open Grad.MainAssembly.CircleIsometryClassification
open Grad.MainAssembly.PhysicalSimilarityRigidity
open Grad.MainAssembly.NormalHessianSeedBridge
open Grad.GeometryClosure

/-- Construction-facing NG_R01--NG_R03 consumer.  Exact axis chart data,
the literal pressure pullback `psi - |y|^2`, and physical criticality produce
the prescribed normalized normal-Hessian shape used by the terminal rigidity
and `MainStatement` packaging chain. -/
theorem hasPrescribedNormalShape_of_axisCharts
    (representative : Representative) (pressure : Vec → ℝ)
    (chart : ℝ → Vec → Vec) (coordinatePoint : ℝ → Vec)
    (potential radius rho alpha delta parameter a : ℝ)
    (tilt : ℝ → Fin 2 → ℝ)
    (represents : ∀ point : Reference,
      pressure (representative.position point) = representative.pressure point)
    (radiusPositive : 0 < radius) (aPositive : 0 < a)
    (rhoLower : -1 < rho) (rhoUpper : rho < 1)
    (chartPoint : ∀ time,
      chart time (coordinatePoint time) = radius • axisRadial time)
    (pressureSmooth : ∀ time,
      ContDiffAt ℝ 2 pressure (chart time (coordinatePoint time)))
    (chartSmooth : ∀ time,
      ContDiffAt ℝ 2 (chart time) (coordinatePoint time))
    (critical : ∀ time,
      fderiv ℝ pressure (chart time (coordinatePoint time)) = 0)
    (pullback : ∀ time,
      (pressure ∘ chart time) =ᶠ[nhds (coordinatePoint time)]
        coordinatePressure potential)
    (axisDerivative : ∀ time,
      HasAxisDerivative (chart time) (coordinatePoint time) radius time a
        (seedMatrix rho
          (HarmonicRigidity.alphaAngle alpha delta parameter time))
        (tilt time)) :
    HasPrescribedNormalShape representative radius rho
      (HarmonicRigidity.alphaAngle alpha delta parameter) := by
  apply hasPrescribedNormalShape_of_seedHessian representative pressure radius
    rho alpha delta parameter a represents aPositive rhoLower rhoUpper
  intro time
  exact physical_normal_hessian_formula pressure (chart time)
    (coordinatePoint time) potential radius time a
    (seedMatrix rho (HarmonicRigidity.alphaAngle alpha delta parameter time))
    (tilt time) radiusPositive.ne' aPositive.ne'
    (isUnit_iff_ne_zero.mpr
      (ne_of_gt (seed_det rhoLower rhoUpper
        (HarmonicRigidity.alphaAngle alpha delta parameter time)).2))
    (chartPoint time) (pressureSmooth time) (chartSmooth time)
    (critical time) (pullback time) (axisDerivative time)

/-- The exact construction-facing data still required at each member of the
physical family after NG_R01--NG_R03: one genuine ambient pressure and one
axis chart whose derivative and pressure pullback have the literal blueprint
form. -/
def HasAxisChartSeedData (representative : Representative)
    (radius rho alpha delta parameter : ℝ) : Prop :=
  ∃ (pressure : Vec → ℝ) (chart : ℝ → Vec → Vec)
    (coordinatePoint : ℝ → Vec) (potential a : ℝ)
    (tilt : ℝ → Fin 2 → ℝ),
    (∀ point : Reference,
      pressure (representative.position point) = representative.pressure point) ∧
    0 < a ∧
    (∀ time, chart time (coordinatePoint time) = radius • axisRadial time) ∧
    (∀ time, ContDiffAt ℝ 2 pressure (chart time (coordinatePoint time))) ∧
    (∀ time, ContDiffAt ℝ 2 (chart time) (coordinatePoint time)) ∧
    (∀ time, fderiv ℝ pressure (chart time (coordinatePoint time)) = 0) ∧
    (∀ time, (pressure ∘ chart time) =ᶠ[nhds (coordinatePoint time)]
      coordinatePressure potential) ∧
    ∀ time,
      HasAxisDerivative (chart time) (coordinatePoint time) radius time a
        (seedMatrix rho
          (HarmonicRigidity.alphaAngle alpha delta parameter time))
        (tilt time)

theorem hasPrescribedNormalShape_of_axisChartSeedData
    (representative : Representative) (radius rho alpha delta parameter : ℝ)
    (radiusPositive : 0 < radius) (rhoLower : -1 < rho) (rhoUpper : rho < 1)
    (data : HasAxisChartSeedData representative radius rho alpha delta parameter) :
    HasPrescribedNormalShape representative radius rho
      (HarmonicRigidity.alphaAngle alpha delta parameter) := by
  rcases data with
    ⟨pressure, chart, coordinatePoint, potential, a, tilt, represents,
      aPositive, chartPoint, pressureSmooth, chartSmooth, critical,
      pullback, axisDerivative⟩
  exact hasPrescribedNormalShape_of_axisCharts representative pressure chart
    coordinatePoint potential radius rho alpha delta parameter a tilt
    represents radiusPositive aPositive rhoLower rhoUpper chartPoint
    pressureSmooth chartSmooth critical pullback axisDerivative

end Grad.MainAssembly.PhysicalNormalHessian.Consumer
