import SCS37PhysicalKernelContinuity

noncomputable section

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision
open Grad.QuotientProjection Grad.GaugeCoefficients.Physical.Allocation Grad.FlatSourceProjection

theorem divisionPolarPoint_periodic (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Function.Periodic (fun angle => polarClosedPoint radius angle nonnegative bounded) (2 * Real.pi) := by
  intro angle
  change polarClosedPoint radius (angle + 2 * Real.pi) nonnegative bounded = polarClosedPoint radius angle nonnegative bounded
  rw [← polarCirclePoint_coe, ← polarCirclePoint_coe, AddCircle.coe_add_period]

theorem physicalDividedSources_polar_periodic (parameters : PhaseParameters) (L : ℝ)
    (source : SmoothQuotient parameters) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (component : Fin 3) (axial : ℝ) :
    Function.Periodic (fun polar => physicalDividedSources parameters L source radius nonnegative bounded component (polar, axial))
      (2 * Real.pi) := by
  intro polar
  have point : polarClosedPoint radius (polar + 2 * Real.pi) nonnegative bounded =
      polarClosedPoint radius polar nonnegative bounded := divisionPolarPoint_periodic radius nonnegative bounded polar
  have radial : radialProjection (polar + 2 * Real.pi) = radialProjection polar := by
    simp only [radialProjection, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have tangential : tangentialProjection (polar + 2 * Real.pi) = tangentialProjection polar := by
    simp only [tangentialProjection, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have corePeriodic {dimension : ℕ} (core : ACore parameters dimension) :
      corePolarValue parameters core radius nonnegative bounded (polar + 2 * Real.pi, axial) =
      corePolarValue parameters core radius nonnegative bounded (polar, axial) := by
    change Grad.SourceCollar.sourceCoreValue core (polarClosedPoint radius (polar + 2 * Real.pi) nonnegative bounded) axial = _
    rw [point]
    rfl
  fin_cases component
  · change radialProjection (polar + 2 * Real.pi) (radius⁻¹ • corePolarValue parameters (cartesianSourceVector source)
      radius nonnegative bounded (polar + 2 * Real.pi, axial)) =
      radialProjection polar (radius⁻¹ • corePolarValue parameters (cartesianSourceVector source) radius nonnegative bounded (polar, axial))
    rw [radial, corePeriodic]
  · change tangentialProjection (polar + 2 * Real.pi) (radius⁻¹ • corePolarValue parameters (cartesianSourceVector source)
      radius nonnegative bounded (polar + 2 * Real.pi, axial)) =
      tangentialProjection polar (radius⁻¹ • corePolarValue parameters (cartesianSourceVector source) radius nonnegative bounded (polar, axial))
    rw [tangential, corePeriodic]
  · change (L : ℂ)⁻¹ • (radius⁻¹ • corePolarValue parameters (source 3) radius nonnegative bounded (polar + 2 * Real.pi, axial)) =
      (L : ℂ)⁻¹ • (radius⁻¹ • corePolarValue parameters (source 3) radius nonnegative bounded (polar, axial))
    rw [corePeriodic]

def physicalCorrection (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (source : SmoothQuotient parameters) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (angles : ℝ × ℝ) : ComplexEuclidean 1 :=
  physicalKappaDeviation parameters L epsilon field radius nonnegative bounded 0 angles •
      physicalDividedSources parameters L source radius nonnegative bounded 0 angles +
    physicalKappaDeviation parameters L epsilon field radius nonnegative bounded 1 angles •
      physicalDividedSources parameters L source radius nonnegative bounded 1 angles -
    physicalKappaDeviation parameters L epsilon field radius nonnegative bounded 2 angles •
      physicalDividedSources parameters L source radius nonnegative bounded 2 angles -
    physicalDividedSources parameters L source radius nonnegative bounded 1 angles

theorem physicalCorrection_continuous (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (source : SmoothQuotient parameters) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Continuous (physicalCorrection parameters L epsilon field source radius nonnegative bounded) := by
  have kernel := physicalKappaDeviation_continuous parameters L rho epsilon field small radius nonnegative bounded
  have sourceContinuous := physicalDividedSources_continuous parameters L source radius nonnegative bounded
  exact (((kernel 0).smul (sourceContinuous 0)).add ((kernel 1).smul (sourceContinuous 1))).sub
    ((kernel 2).smul (sourceContinuous 2)) |>.sub (sourceContinuous 1)

theorem physicalCorrection_polar_periodic (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (source : SmoothQuotient parameters) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (axial : ℝ) :
    Function.Periodic (fun polar => physicalCorrection parameters L epsilon field source radius nonnegative bounded (polar, axial))
      (2 * Real.pi) := by
  intro polar
  have kernel (component : Fin 3) :
      physicalKappaDeviation parameters L epsilon field radius nonnegative bounded component (polar + 2 * Real.pi, axial) =
      physicalKappaDeviation parameters L epsilon field radius nonnegative bounded component (polar, axial) :=
    physicalKappaDeviation_polar_periodic parameters L rho epsilon field small radius nonnegative bounded component axial polar
  have sourceLaw (component : Fin 3) :
      physicalDividedSources parameters L source radius nonnegative bounded component (polar + 2 * Real.pi, axial) =
      physicalDividedSources parameters L source radius nonnegative bounded component (polar, axial) :=
    physicalDividedSources_polar_periodic parameters L source radius nonnegative bounded component axial polar
  simp only [physicalCorrection, kernel, sourceLaw]

end Grad.SourceCollarFullSource
