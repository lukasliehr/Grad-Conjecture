import ANR27RadialFluxCalculus

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace

def diskRadialValue (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : diskGrade) : CollarL2 (ComplexEuclidean 1) lower :=
  collarH1Coordinate (ComplexEuclidean 1) lower 0
    (weightedToOrdinary 1 lower positive bounded (diskRadial lower positive bounded mode field))

def diskRadialSlope (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : diskGrade) : CollarL2 (ComplexEuclidean 1) lower :=
  collarH1Coordinate (ComplexEuclidean 1) lower 1
    (weightedToOrdinary 1 lower positive bounded (diskRadial lower positive bounded mode field))

def weakRadialLaplacian (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) : CollarL2 (ComplexEuclidean 1) lower :=
  radialOrdinary 1 lower positive (diskL2Radial lower positive bounded mode (weakLaplacianValue parameter source))

def weakRadialFlux (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) : CollarL2 (ComplexEuclidean 1) lower :=
  collarScalar 1 lower radialRadiusCurve
    (diskRadialSlope lower positive bounded mode (highRobinWeakInverse parameter source).val)

def weakRadialFluxDerivative (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) : CollarL2 (ComplexEuclidean 1) lower :=
  collarScalar 1 lower (radialPotentialCurve lower positive mode)
    (diskRadialValue lower positive bounded mode (highRobinWeakInverse parameter source).val) +
  collarScalar 1 lower radialRadiusCurve (weakRadialLaplacian lower positive bounded mode parameter source)

/-- The same actual AN18 field satisfies (r z_m')' = (m²/r)z_m + r(Δz)_m
against the original compact C∞ radial tests. -/
theorem weakInverse_radial_flux (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) :
    CompactWeakDerivative 1 lower
      (weakRadialFlux lower positive bounded mode parameter source)
      (weakRadialFluxDerivative lower positive bounded mode parameter source) := by
  apply radial_secondTest_to_flux lower positive mode
    (diskRadialValue lower positive bounded mode (highRobinWeakInverse parameter source).val)
    (diskRadialSlope lower positive bounded mode (highRobinWeakInverse parameter source).val)
    (weakRadialLaplacian lower positive bounded mode parameter source)
    (diskRadial_weakDerivative lower positive bounded mode _)
  intro test smooth supported vector
  let operatorMap : C(ℝ, ℝ) := ⟨fun radius => radius * radialTestOperator mode test radius,
    continuous_id.mul (radialTestOperator_smooth mode test smooth
      (collar_supported_inside lower positive test supported)).continuous⟩
  let testMap : C(ℝ, ℝ) := ⟨fun radius => radius * test radius, continuous_id.mul smooth.continuous⟩
  let bulk := diskL2Radial lower positive bounded mode (highDiskBulk (highRobinWeakInverse parameter source))
  let laplacian := diskL2Radial lower positive bounded mode (weakLaplacianValue parameter source)
  have left := radialPairing_ordinary 1 lower positive operatorMap vector bulk
  have right := radialPairing_ordinary 1 lower positive testMap vector laplacian
  have second := weakInverse_radial_secondTest lower positive bounded parameter source mode vector test smooth supported
  have result := left.symm.trans (second.trans right)
  have bulkLaw : radialOrdinary 1 lower positive bulk =
      diskRadialValue lower positive bounded mode (highRobinWeakInverse parameter source).val :=
    diskRadial_ordinary_bulk lower positive bounded mode _
  exact (congrArg (collarPairing lower operatorMap vector) bulkLaw).symm.trans result

theorem weakRadialFlux_ae (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      weakRadialFlux lower positive bounded mode parameter source radius =
        radius • diskRadialSlope lower positive bounded mode (highRobinWeakInverse parameter source).val radius :=
  collarScalar_ae 1 lower radialRadiusCurve _

theorem weakRadialFluxDerivative_ae (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      weakRadialFluxDerivative lower positive bounded mode parameter source radius =
        ((mode : ℝ) ^ 2 / radius) • diskRadialValue lower positive bounded mode
          (highRobinWeakInverse parameter source).val radius +
        radius • weakRadialLaplacian lower positive bounded mode parameter source radius := by
  filter_upwards [Lp.coeFn_add
    (collarScalar 1 lower (radialPotentialCurve lower positive mode)
      (diskRadialValue lower positive bounded mode (highRobinWeakInverse parameter source).val))
    (collarScalar 1 lower radialRadiusCurve (weakRadialLaplacian lower positive bounded mode parameter source)),
    collarScalar_ae 1 lower (radialPotentialCurve lower positive mode)
      (diskRadialValue lower positive bounded mode (highRobinWeakInverse parameter source).val),
    collarScalar_ae 1 lower radialRadiusCurve (weakRadialLaplacian lower positive bounded mode parameter source),
    ae_restrict_mem measurableSet_Icc] with radius addition first second inside
  dsimp only [Pi.add_apply] at addition
  exact addition.trans (congrArg₂ (fun first second : ComplexEuclidean 1 => first + second)
    (first.trans (congrArg (fun scalar : ℝ => scalar • diskRadialValue lower positive bounded mode
      (highRobinWeakInverse parameter source).val radius)
      (radialPotentialCurve_literal lower positive mode radius inside.1))) second)

/-- V4's first weak-to-continuous step for the constructed inverse, with
the literal closed-collar anchored integral and a.e. equality to r z_m'. -/
theorem weakInverse_radial_flux_representative (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) :
    ∃ representative : RadialContinuousSection 1 lower,
      (∀ᵐ radius ∂volume.restrict (Icc lower 1),
        radialSectionExtension 1 lower bounded.le representative radius =
          radius • diskRadialSlope lower positive bounded.le mode (highRobinWeakInverse parameter source).val radius) ∧
      ∀ radius : Icc lower (1 : ℝ),
        representative radius = representative ⟨lower, le_rfl, bounded.le⟩ +
          ∫ point in lower..radius.val, weakRadialFluxDerivative lower positive bounded.le mode parameter source point := by
  let flux : CollarL2 (ComplexEuclidean 1) lower := weakRadialFlux lower positive bounded.le mode parameter source
  let forcing : CollarL2 (ComplexEuclidean 1) lower := weakRadialFluxDerivative lower positive bounded.le mode parameter source
  have law : CompactWeakDerivative 1 lower flux forcing :=
    weakInverse_radial_flux lower positive bounded.le mode parameter source
  have existence := actualCompactWeakRadialRepresentative 1 lower positive bounded flux forcing law
  obtain ⟨representative, actual, primitive⟩ := existence
  refine ⟨representative, ?_, primitive⟩
  filter_upwards [actual, weakRadialFlux_ae lower positive bounded.le mode parameter source]
    with radius first second
  exact first.trans second

end Grad.CircularHighRegularity
