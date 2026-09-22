import ANU4CoherentBoundaryForcing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualForcingSupport
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.ActualScalarForcing Grad.BoundedScalarInverse Grad.RawCircularSectors
variable {L sigma gamma ell : ℝ}

/-- All four actual input conditions of the bounded scalar solver follow from
original cap support and the source's raw exclusions. -/
theorem actualForcedScalarInputs (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (source : SmoothCapSource L sigma gamma ell) (excluded : AvoidsExceptionalSource source)
    (sourceBand : OriginalCapSourceBand admissible ceiling source)
    (beta : BandSmoothBoundary L sigma gamma ell) (betaBand : OriginalBoundaryBand ceiling beta) :
    OriginalSourceNonexceptional admissible (scalarForcing admissible source) ∧
      OriginalSourceBand admissible ceiling (scalarForcing admissible source) ∧
        OriginalBoundaryHigh (forcedBoundary admissible source beta) ∧
          OriginalBoundaryBand ceiling (forcedBoundary admissible source beta) :=
  ⟨scalarForcing_nonexceptional admissible source excluded, scalarForcing_band admissible ceiling source sourceBand,
    forcedBoundary_high admissible source beta, forcedBoundary_band admissible ceiling source sourceBand beta betaBand⟩

/-- A single actual original AP scalar solution for the original AN15/16 data.
The estimate retains the exact frozen ANF constants and has no ell or cell-count
dependence. The original analytic width and displayed Sobolev grades are used. -/
theorem actualForcedScalarSolution (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (parameters : PhaseParameters)
    (source : SmoothCapSource L sigma gamma ell) (excluded : AvoidsExceptionalSource source)
    (sourceBand : OriginalCapSourceBand admissible ceiling source)
    (beta : BandSmoothBoundary L sigma gamma ell) (betaBand : OriginalBoundaryBand ceiling beta) :
    ∃! solution : APSmooth L sigma gamma ell 1,
      IsOriginalScalarSolution admissible (scalarForcing admissible source) (forcedBoundary admissible source beta) solution ∧
      OriginalSourceBand admissible ceiling solution ∧
      ∀ (grade : ℕ) (large : 3 ≤ grade),
        ‖apSmoothGrade L sigma gamma ell 1 (grade + 2) solution‖ ≤
          bandScalarGainConstant L gamma ceiling grade large *
            ((forcingConstant L gamma grade + boundaryForcingConstant L sigma gamma grade) *
              ‖capSourceGrade grade source‖ + ‖beta.grade grade‖) := by
  have conditions := actualForcedScalarInputs admissible ceiling source excluded sourceBand beta betaBand
  let solution := apBandScalarInverse admissible ceiling parameters (scalarForcing admissible source)
    conditions.1 (forcedBoundary admissible source beta) conditions.2.2.1
  refine ⟨solution, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact apBandScalarInverse_specification admissible ceiling parameters _ conditions.1 conditions.2.1 _ conditions.2.2.1 conditions.2.2.2
  · exact apBandScalarInverse_support admissible ceiling parameters _ conditions.1 _ conditions.2.2.1
  · intro grade large
    exact (apBandScalarInverse_native_gain admissible ceiling parameters _ conditions.1 _ conditions.2.2.1 grade large).trans
      (mul_le_mul_of_nonneg_left (forcedData_native_bound admissible grade source beta)
        (bandScalarGainConstant_nonnegative L gamma ceiling (admissible_gamma_nonnegative admissible) grade large))
  · intro candidate laws
    exact apBandScalarInverse_unique admissible ceiling parameters _ conditions.1 conditions.2.1 _ conditions.2.2.1 conditions.2.2.2 candidate laws.1

end Grad.ActualForcingSupport
