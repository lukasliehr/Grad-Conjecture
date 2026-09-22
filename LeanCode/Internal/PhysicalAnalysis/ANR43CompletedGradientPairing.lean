import ANR42CollarGradientIntegral

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryTrace
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace

def diskCoreRadialSlopeCurve (mode : ℤ) (field : ClosedJet 1) : C(ℝ, ComplexEuclidean 1) :=
  ⟨radialCoefficientJet (originalPolarValue field) mode 1,
    (radialCoefficientJet_smooth _ (originalPolarValue_smooth field) mode 1).continuous⟩

theorem diskRadialValue_core (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : ClosedJet 1) :
    diskRadialValue lower positive bounded mode (diskCoreInto field) =
      collarContinuousL2 (ComplexEuclidean 1) lower (diskCoreRadialCurve mode field) := by
  have graph := (congrArg (weightedToOrdinary 1 lower positive bounded) (diskRadial_core lower positive bounded mode field)).trans
    (weightedToOrdinary_core 1 lower positive bounded (diskRadialSmoothCore mode field))
  exact congrArg (collarH1Coordinate (ComplexEuclidean 1) lower 0) graph

theorem diskRadialSlope_core (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : ClosedJet 1) :
    diskRadialSlope lower positive bounded mode (diskCoreInto field) =
      collarContinuousL2 (ComplexEuclidean 1) lower (diskCoreRadialSlopeCurve mode field) := by
  have graph := (congrArg (weightedToOrdinary 1 lower positive bounded) (diskRadial_core lower positive bounded mode field)).trans
    (weightedToOrdinary_core 1 lower positive bounded (diskRadialSmoothCore mode field))
  exact congrArg (collarH1Coordinate (ComplexEuclidean 1) lower 1) graph

theorem diskRadialValue_continuous (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (mode : ℤ) :
    Continuous (diskRadialValue lower positive bounded mode) :=
  (collarH1Coordinate (ComplexEuclidean 1) lower 0).continuous.comp
    ((weightedToOrdinary 1 lower positive bounded).continuous.comp (diskRadial lower positive bounded mode).continuous)

theorem diskRadialSlope_continuous (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (mode : ℤ) :
    Continuous (diskRadialSlope lower positive bounded mode) :=
  (collarH1Coordinate (ComplexEuclidean 1) lower 1).continuous.comp
    ((weightedToOrdinary 1 lower positive bounded).continuous.comp (diskRadial lower positive bounded mode).continuous)

/-- The genuine completed disk H1 gradient pairing against an arbitrary
outer-boundary character test, in the same ordinary radial coordinates. -/
theorem boundaryCharacter_gradient_completed (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test)
    (supported : tsupport test ⊆ Ioi lower) (field : diskGrade) :
    inner ℂ (diskGradX (diskCoreInto (boundaryCharacterJet mode vector test smooth (collarSupport_away lower positive test supported))))
        (diskGradX field) +
      inner ℂ (diskGradY (diskCoreInto (boundaryCharacterJet mode vector test smooth (collarSupport_away lower positive test supported))))
        (diskGradY field) =
    (2 * Real.pi) •
      (collarPairing lower ⟨fun radius => radius * deriv test radius,
        continuous_id.mul (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩ vector
        (diskRadialSlope lower positive bounded mode field) +
      collarPairing lower ⟨fun radius => test radius * radialPotentialCurve lower positive mode radius,
        smooth.continuous.mul (radialPotentialCurve lower positive mode).continuous⟩ vector
        (diskRadialValue lower positive bounded mode field)) := by
  let jet := boundaryCharacterJet mode vector test smooth (collarSupport_away lower positive test supported)
  let firstTest : C(ℝ, ℝ) := ⟨fun radius => radius * deriv test radius,
    continuous_id.mul (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩
  let secondTest : C(ℝ, ℝ) := ⟨fun radius => test radius * radialPotentialCurve lower positive mode radius,
    smooth.continuous.mul (radialPotentialCurve lower positive mode).continuous⟩
  have leftContinuous : Continuous (fun field : diskGrade =>
      inner ℂ (diskGradX (diskCoreInto jet)) (diskGradX field) + inner ℂ (diskGradY (diskCoreInto jet)) (diskGradY field)) :=
    ((innerSL ℂ (diskGradX (diskCoreInto jet))).continuous.comp diskGradX.continuous).add
      ((innerSL ℂ (diskGradY (diskCoreInto jet))).continuous.comp diskGradY.continuous)
  have rightContinuous : Continuous (fun field : diskGrade => (2 * Real.pi) •
      (collarPairing lower firstTest vector (diskRadialSlope lower positive bounded mode field) +
        collarPairing lower secondTest vector (diskRadialValue lower positive bounded mode field))) :=
    (((collarPairing lower firstTest vector).continuous.comp (diskRadialSlope_continuous lower positive bounded mode)).add
      ((collarPairing lower secondTest vector).continuous.comp (diskRadialValue_continuous lower positive bounded mode))).const_smul
        (2 * Real.pi : ℝ)
  apply isClosed_property diskCoreInto_denseRange (isClosed_eq leftContinuous rightContinuous) _ field
  intro core
  have first := (congrArg (collarPairing lower firstTest vector) (diskRadialSlope_core lower positive bounded mode core)).trans
    (collarPairing_core lower bounded firstTest vector (diskCoreRadialSlopeCurve mode core))
  have second := (congrArg (collarPairing lower secondTest vector) (diskRadialValue_core lower positive bounded mode core)).trans
    (collarPairing_core lower bounded secondTest vector (diskCoreRadialCurve mode core))
  have firstIntegrable : IntervalIntegrable (fun radius => firstTest radius • inner ℂ vector (diskCoreRadialSlopeCurve mode core radius))
      volume lower 1 := (firstTest.continuous.smul ((innerSL ℂ vector).continuous.comp (diskCoreRadialSlopeCurve mode core).continuous)).intervalIntegrable _ _
  have secondIntegrable : IntervalIntegrable (fun radius => secondTest radius • inner ℂ vector (diskCoreRadialCurve mode core radius))
      volume lower 1 := (secondTest.continuous.smul ((innerSL ℂ vector).continuous.comp (diskCoreRadialCurve mode core).continuous)).intervalIntegrable _ _
  have sums := congrArg₂ (fun first second : ℂ => first + second) first second
  have integral := intervalIntegral.integral_add (μ := volume) firstIntegrable secondIntegrable
  exact (boundaryCharacter_gradient_collar_core lower positive bounded mode vector test smooth supported core).trans
    (congrArg (fun value : ℂ => (2 * Real.pi) • value) (integral.trans sums.symm))

end Grad.CircularHighRegularity
