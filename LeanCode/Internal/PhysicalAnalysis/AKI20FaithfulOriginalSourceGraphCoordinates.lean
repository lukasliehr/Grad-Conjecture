import AKI19SameInverseLiteralCoreMember

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCurrentLow Grad.AnnularCurrentSource
open Grad.AnnularSourceGraph Grad.AnnularFullGraph Grad.AnnularReconstruction

theorem lowRhoPhysicalCoefficient_faithful {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) {first second : DivisionRow dimension lower}
    (same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      lowRhoPhysicalCoefficient parameters lower positive first radius mode =
        lowRhoPhysicalCoefficient parameters lower positive second radius mode) : first = second := by
  apply lp.ext
  funext mode
  apply Lp.ext
  filter_upwards [same] with radius equal
  exact (smul_right_injective (ComplexEuclidean dimension)
    (inv_ne_zero (Complex.ofReal_ne_zero.mpr (lowRhoPhysicalWeight_pos parameters lower positive radius mode).ne'))) (equal mode)

theorem originalF1Coefficient_faithful (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) {first second : DivisionRow 1 lower}
    (same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      originalF1Coefficient parameters lower positive bounded first radius mode =
        originalF1Coefficient parameters lower positive bounded second radius mode) : first = second :=
  (originalBulkWeightEquivalence lower positive bounded).injective
    (lowRhoPhysicalCoefficient_faithful parameters lower positive same)

/-- Original split-grade F0 values determine its complete genuine H1 graph,
including the stored radial derivative and both endpoints. -/
theorem unweightedSourceF0Bulk_faithful (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) : Function.Injective (unweightedSourceF0Bulk parameters lower) := by
  intro first second same
  apply annularSource_bulk_injective parameters 1 lower positive bounded 1 0
  apply lp.ext
  funext mode
  have coefficient := congrArg (fun row : DivisionRow 1 lower => row mode) same
  change sourceGradeRatio 0 0 1 0 mode • weightedRadialCoordinate 1 lower 0 (first mode) =
    sourceGradeRatio 0 0 1 0 mode • weightedRadialCoordinate 1 lower 0 (second mode) at coefficient
  exact (smul_right_injective (RadialL2 1 lower) (sourceGradeRatio_pos 0 0 1 0 mode).ne') coefficient

theorem unweightedSourceF2Bulk_faithful (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) : Function.Injective (unweightedSourceF2Bulk parameters lower) :=
  annularSource_bulk_injective parameters 1 lower positive bounded 0 0

/-- The represented source/residual block has no independent derivative or
trace freedom: all four complete original graph coordinates are fixed by
the literal tuple. In particular no source derivative is made by projection. -/
theorem OriginalTupleObservation.sourceBlocks_unique {parameters : PhaseParameters} {length compact lower : ℝ}
    {positive : 0 < lower} {bounded : lower < 1} {lengthPositive : 0 < length}
    {state : RetainedInverseState parameters length compact} {tuple : OriginalSmoothTuple parameters lower}
    {first second : OriginalFiveBlockAmbient parameters lower length positive}
    (firstSame : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple first)
    (secondSame : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple second) :
    first.ofLp.2 = second.ofLp.2 := by
  have f0 : first.ofLp.2.ofLp.1.ofLp.1 = second.ofLp.2.ofLp.1.ofLp.1 := by
    apply unweightedSourceF0Bulk_faithful parameters lower positive bounded.le
    apply originalF1Coefficient_faithful parameters lower positive bounded.le
    filter_upwards [firstSame.sourceZero, secondSame.sourceZero] with radius first second
    exact fun mode => (first mode).symm.trans (second mode)
  have f2 : first.ofLp.2.ofLp.1.ofLp.2 = second.ofLp.2.ofLp.1.ofLp.2 := by
    apply unweightedSourceF2Bulk_faithful parameters lower positive bounded.le
    apply originalF1Coefficient_faithful parameters lower positive bounded.le
    filter_upwards [firstSame.sourceTwo, secondSame.sourceTwo] with radius first second
    exact fun mode => (first mode).symm.trans (second mode)
  have f : first.ofLp.2.ofLp.2.ofLp.1 = second.ofLp.2.ofLp.2.ofLp.1 := by
    apply originalF1Coefficient_faithful parameters lower positive bounded.le
    filter_upwards [firstSame.firstResidual, secondSame.firstResidual, ae_restrict_mem measurableSet_Icc] with radius first second inside
    exact fun mode => (first inside mode).symm.trans (second inside mode)
  have g : first.ofLp.2.ofLp.2.ofLp.2 = second.ofLp.2.ofLp.2.ofLp.2 := by
    apply originalF1Coefficient_faithful parameters lower positive bounded.le
    filter_upwards [firstSame.strengthenedThird, secondSame.strengthenedThird, ae_restrict_mem measurableSet_Icc] with radius first second inside
    exact fun mode => (first inside mode).symm.trans (second inside mode)
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · exact (WithLp.equiv 2 _).injective (Prod.ext f0 f2)
  · exact (WithLp.equiv 2 _).injective (Prod.ext f g)

end Grad.AnnularOriginalSmoothCore
