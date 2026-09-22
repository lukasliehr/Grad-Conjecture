import ANR49ActualOuterFlux

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The upper trace of an actual H1 flux r u' is the literal one-sided
derivative of the same continuous value representative at r=1. -/
theorem weightedRadial_outer_derivative (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (value flux : WeightedRadialH1 dimension lower)
    (actual : ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      collarH1Coordinate (ComplexEuclidean dimension) lower 0 (weightedToOrdinary dimension lower positive bounded.le flux) radius =
        radius • collarH1Coordinate (ComplexEuclidean dimension) lower 1
          (weightedToOrdinary dimension lower positive bounded.le value) radius) :
    HasDerivWithinAt
      (radialSectionExtension dimension lower bounded.le (weightedRadialSection dimension lower positive bounded value))
      (weightedRadialTrace dimension lower positive bounded 1 flux) (Icc lower 1) 1 := by
  let sectionValue := weightedRadialSection dimension lower positive bounded value
  let sectionFlux := weightedRadialSection dimension lower positive bounded flux
  let extension := radialSectionExtension dimension lower bounded.le sectionFlux
  let slope := collarH1Coordinate (ComplexEuclidean dimension) lower 1
    (weightedToOrdinary dimension lower positive bounded.le value)
  have fluxAE : ∀ᵐ radius ∂volume.restrict (Icc lower 1), extension radius = radius • slope radius :=
    Filter.EventuallyEq.trans (weightedRadialSection_ae dimension lower positive bounded flux) actual
  let inverse := radialInverseRadiusCurve lower positive
  let derivative : C(ℝ, ComplexEuclidean dimension) :=
    ⟨fun radius => inverse radius • extension radius, inverse.continuous.smul extension.continuous⟩
  have same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), derivative radius = slope radius :=
    radialFlux_decode dimension lower positive extension slope fluxAE
  have primitive (radius : Icc lower (1 : ℝ)) :
      sectionValue radius = sectionValue ⟨lower, le_rfl, bounded.le⟩ + ∫ point in lower..radius.val, slope point := by
    have law := weightedRadialSection_primitive dimension lower positive bounded value radius
    have endpoint := weightedRadialSection_endpoint dimension lower positive bounded 0 value
    exact law.trans (congrArg (fun anchor : ComplexEuclidean dimension => anchor +
      ∫ point in lower..radius.val, slope point) endpoint.symm)
  have derivativeLaw := radialSection_hasDerivWithinAt dimension lower bounded.le sectionValue slope derivative
    (Filter.EventuallyEq.symm same) primitive 1 ⟨bounded.le, le_rfl⟩
  have endpoint : derivative 1 = weightedRadialTrace dimension lower positive bounded 1 flux := by
    change (max lower 1)⁻¹ • sectionFlux (radialClamp lower bounded.le 1) = _
    rw [max_eq_right bounded.le, inv_one, one_smul, radialClamp_eq lower bounded.le 1 ⟨bounded.le, le_rfl⟩]
    exact weightedRadialSection_endpoint dimension lower positive bounded 1 flux
  exact derivativeLaw.congr_deriv endpoint

/-- Literal Robin recovery for every actual L2 source. No normal trace or
strong regularity is assumed: the one-sided derivative follows from the
proved weak flux and its graph endpoints. -/
theorem weakInverse_literal_robin (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (mode : ℤ) (high : mode ∉ lowAngularModes) :
    let value := radialSectionExtension 1 lower bounded.le
      (diskRadialValueSection lower positive bounded mode (highRobinWeakInverse parameter source).val)
    HasDerivWithinAt value (-(2 : ℝ) • value 1) (Icc lower 1) 1 := by
  have existence := weakInverse_outer_flux lower positive bounded parameter source mode high
  obtain ⟨flux, valueLaw, _slopeLaw, robin⟩ := existence
  let value := diskRadial lower positive bounded.le mode (highRobinWeakInverse parameter source).val
  have actual : ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      collarH1Coordinate (ComplexEuclidean 1) lower 0 (weightedToOrdinary 1 lower positive bounded.le flux) radius =
        radius • collarH1Coordinate (ComplexEuclidean 1) lower 1
          (weightedToOrdinary 1 lower positive bounded.le value) radius := by
    have law := weakRadialFlux_ae lower positive bounded.le mode parameter source
    exact Filter.EventuallyEq.trans (Filter.Eventually.of_forall (fun radius => congrArg (fun field : CollarL2 (ComplexEuclidean 1) lower => field radius) valueLaw)) law
  have derivativeLaw := weightedRadial_outer_derivative 1 lower positive bounded value flux actual
  have outer : radialSectionExtension 1 lower bounded.le
      (diskRadialValueSection lower positive bounded mode (highRobinWeakInverse parameter source).val) 1 =
        diskBoundaryFourier (highRobinWeakInverse parameter source).val (mode, 0) := by
    exact (congrArg (diskRadialValueSection lower positive bounded mode (highRobinWeakInverse parameter source).val)
      (radialClamp_eq lower bounded.le 1 ⟨bounded.le, le_rfl⟩)).trans
        (diskRadialValueSection_upper lower positive bounded mode _)
  have fluxLaw : weightedRadialTrace 1 lower positive bounded 1 flux =
      -(2 : ℝ) • radialSectionExtension 1 lower bounded.le
        (diskRadialValueSection lower positive bounded mode (highRobinWeakInverse parameter source).val) 1 := by
    have negative := eq_neg_of_add_eq_zero_left robin
    exact negative.trans ((neg_smul (2 : ℝ) _).symm.trans (congrArg (fun field : ComplexEuclidean 1 => -(2 : ℝ) • field) outer.symm))
  exact derivativeLaw.congr_deriv fluxLaw

end Grad.CircularHighRegularity
