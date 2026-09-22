import ANR31LiteralSmoothRadialSource

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace

private theorem radialForcing_representative (lower : ℝ) (positive : 0 < lower) (mode : ℤ) (scalar : ℂ)
    (value laplacian forcing : CollarL2 (ComplexEuclidean 1) lower)
    (representative source : C(ℝ, ComplexEuclidean 1))
    (forcingLaw : ∀ᵐ radius ∂volume.restrict (Icc lower 1), forcing radius =
      ((mode : ℝ) ^ 2 / radius) • value radius + radius • laplacian radius)
    (laplacianLaw : ∀ᵐ radius ∂volume.restrict (Icc lower 1), laplacian radius = scalar • value radius - source radius)
    (valueLaw : ∀ᵐ radius ∂volume.restrict (Icc lower 1), representative radius = value radius) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), forcing radius =
      radialPotentialCurve lower positive mode radius • representative radius +
        radius • (scalar • representative radius - source radius) := by
  filter_upwards [forcingLaw, laplacianLaw, valueLaw, ae_restrict_mem measurableSet_Icc]
    with radius first second third inside
  rw [first, second, ← third, radialPotentialCurve_literal lower positive mode radius inside.1]

/-- The actual inverse coefficient and its actual flux solve the classical
first-order AN19 system on the closed collar, including both endpoints. -/
theorem weakInverse_classical_radial_system (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (high : mode ∉ lowAngularModes) (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    let value := radialSectionExtension 1 lower bounded.le
      (diskRadialValueSection lower positive bounded mode (highRobinWeakInverse parameter source).val)
    ∃ flux : C(ℝ, ComplexEuclidean 1),
      (∀ᵐ radius ∂volume.restrict (Icc lower 1), flux radius =
        radius • diskRadialSlope lower positive bounded.le mode (highRobinWeakInverse parameter source).val radius) ∧
      (∀ radius ∈ Icc lower 1, HasDerivWithinAt value (radius⁻¹ • flux radius) (Icc lower 1) radius) ∧
      ∀ radius ∈ Icc lower 1, HasDerivWithinAt flux
        (((mode : ℝ) ^ 2 / radius) • value radius +
          radius • ((((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ) • value radius -
            diskCoreRadialCurve mode core radius)) (Icc lower 1) radius := by
  dsimp only
  let solution := (highRobinWeakInverse parameter source).val
  let valueSection := diskRadialValueSection lower positive bounded mode solution
  let value := radialSectionExtension 1 lower bounded.le valueSection
  have existence := weakInverse_radial_flux_representative lower positive bounded mode parameter source
  obtain ⟨fluxSection, fluxActual, fluxPrimitive⟩ := existence
  let flux := radialSectionExtension 1 lower bounded.le fluxSection
  let inverse := radialInverseRadiusCurve lower positive
  let derivative : C(ℝ, ComplexEuclidean 1) :=
    ⟨fun radius => inverse radius • flux radius, inverse.continuous.smul flux.continuous⟩
  let scalar : ℂ := (((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ)
  let forcing : C(ℝ, ComplexEuclidean 1) :=
    ⟨fun radius => radialPotentialCurve lower positive mode radius • value radius +
      radius • (scalar • value radius - diskCoreRadialCurve mode core radius),
      ((radialPotentialCurve lower positive mode).continuous.smul value.continuous).add
        (continuous_id.smul ((value.continuous.const_smul scalar).sub (diskCoreRadialCurve mode core).continuous))⟩
  have derivativeActual : (diskRadialSlope lower positive bounded.le mode solution : ℝ → ComplexEuclidean 1) =ᵐ[
      volume.restrict (Icc lower 1)] derivative :=
    Filter.EventuallyEq.symm (radialFlux_decode 1 lower positive flux
      (diskRadialSlope lower positive bounded.le mode solution) fluxActual)
  have forcingActual : (weakRadialFluxDerivative lower positive bounded.le mode parameter source : ℝ → ComplexEuclidean 1) =ᵐ[
      volume.restrict (Icc lower 1)] forcing :=
    radialForcing_representative lower positive mode scalar
      (diskRadialValue lower positive bounded.le mode solution)
      (weakRadialLaplacian lower positive bounded.le mode parameter source)
      (weakRadialFluxDerivative lower positive bounded.le mode parameter source) value (diskCoreRadialCurve mode core)
      (weakRadialFluxDerivative_ae lower positive bounded.le mode parameter source)
      (weakRadialLaplacian_smoothSource_ae lower positive bounded.le mode high parameter source core same)
      (diskRadialValueSection_ae lower positive bounded mode solution)
  refine ⟨flux, fluxActual, ?_, ?_⟩
  · intro radius inside
    have result := radialSection_hasDerivWithinAt 1 lower bounded.le valueSection
      (diskRadialSlope lower positive bounded.le mode solution) derivative derivativeActual
      (diskRadialValueSection_primitive lower positive bounded mode solution) radius inside
    have literal : derivative radius = radius⁻¹ • flux radius := by
      change (max lower radius)⁻¹ • flux radius = _
      rw [max_eq_right inside.1]
    exact result.congr_deriv literal
  · intro radius inside
    have result := radialSection_hasDerivWithinAt 1 lower bounded.le fluxSection
      (weakRadialFluxDerivative lower positive bounded.le mode parameter source) forcing forcingActual
      fluxPrimitive radius inside
    have literal : forcing radius = ((mode : ℝ) ^ 2 / radius) • value radius +
        radius • (scalar • value radius - diskCoreRadialCurve mode core radius) := by
      change radialPotentialCurve lower positive mode radius • value radius + _ = _
      rw [radialPotentialCurve_literal lower positive mode radius inside.1]
    exact result.congr_deriv literal

end Grad.CircularHighRegularity
