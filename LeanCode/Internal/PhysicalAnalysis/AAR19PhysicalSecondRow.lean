import AAR18NormalizedSecondRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem annularPhase_algebra {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (unphase radial phase potential : E →L[ℝ] E) (u q g h : E)
    (radialQ : unphase (radial q) = radial (unphase q))
    (potentialU : unphase (potential u) = potential (unphase u))
    (radialTwiceU : unphase (radial (radial u)) = radial (radial (unphase u))) :
    -unphase (phase q) + unphase (phase q + radial q + potential u -
      (4 : ℝ) • radial (radial u) - g - h) =
    radial (unphase q) + potential (unphase u) -
      (4 : ℝ) • radial (radial (unphase u)) - unphase g - unphase h := by
  simp only [map_add, map_sub, map_smul]
  rw [radialQ, potentialU, radialTwiceU]
  abel

section SecondRow
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- AG23 after removal of the actual curved phase. The potential-minus-four
term is written as its literal scalar operators; all cells remain present. -/
theorem annularPhysicalQSlope_formula (bounded : lower ≤ 1)
    (field : annularEnergySpace lower length positive) (source : AnnularForcing lower) (mode : HighAnnularMode) :
    let q := annularPhysicalQ parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode
    let xi := annularPhysicalValue parameters lower length positive bounded mode field
    annularPhysicalQSlope parameters lower length positive lengthPositive widthHalf widthLength bounded field source mode =
      collarScalar 1 lower (annularInverseRadiusCurve lower positive) q +
      collarScalar 1 lower (annularPotentialCurve lower length positive mode) xi -
      (4 : ℝ) • collarScalar 1 lower (annularInverseRadiusCurve lower positive)
        (collarScalar 1 lower (annularInverseRadiusCurve lower positive) xi) -
      annularDSymbol mode • annularDecodeMode parameters lower positive mode (source.2.1 mode) -
      annularCellSymbol length mode • annularDecodeMode parameters lower positive mode (source.2.2.1 mode) := by
  dsimp only
  unfold annularPhysicalQSlope
  rw [inversePhaseSlope_cancellation,
    annularNormalizedQSlope_formula parameters lower length positive lengthPositive widthHalf widthLength bounded field source mode]
  dsimp only
  let inverse := annularInversePhase parameters mode.val.2
  let radial := annularInverseRadiusCurve lower positive
  let potential := annularPotentialCurve lower length positive mode
  let phase := annularPhaseCurve parameters mode.val.2
  let q := radialOrdinary 1 lower positive
    (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode)
  let u := annularOrdinaryCoordinate lower length positive bounded mode 0 field
  let g := radialOrdinary 1 lower positive (source.2.1 mode)
  let h := radialOrdinary 1 lower positive (source.2.2.1 mode)
  have twice := (collarScalar_comm lower inverse radial (collarScalar 1 lower radial u)).trans
    (congrArg (collarScalar 1 lower radial) (collarScalar_comm lower inverse radial u))
  have algebra := annularPhase_algebra
    ((collarScalar 1 lower inverse).restrictScalars ℝ)
    ((collarScalar 1 lower radial).restrictScalars ℝ)
    ((collarScalar 1 lower phase).restrictScalars ℝ)
    ((collarScalar 1 lower potential).restrictScalars ℝ)
    u q (annularDSymbol mode • g) (annularCellSymbol length mode • h)
    (collarScalar_comm lower inverse radial q) (collarScalar_comm lower inverse potential u) twice
  change -collarScalar 1 lower inverse (collarScalar 1 lower phase q) +
    collarScalar 1 lower inverse (collarScalar 1 lower phase q + collarScalar 1 lower radial q +
      collarScalar 1 lower potential u - (4 : ℝ) • collarScalar 1 lower radial (collarScalar 1 lower radial u) -
      annularDSymbol mode • g - annularCellSymbol length mode • h) =
    collarScalar 1 lower radial (collarScalar 1 lower inverse q) +
      collarScalar 1 lower potential (collarScalar 1 lower inverse u) -
      (4 : ℝ) • collarScalar 1 lower radial (collarScalar 1 lower radial (collarScalar 1 lower inverse u)) -
      collarScalar 1 lower inverse (annularDSymbol mode • g) -
      collarScalar 1 lower inverse (annularCellSymbol length mode • h) at algebra
  have mappedG := (collarScalar 1 lower inverse).map_smul (annularDSymbol mode) g
  have mappedH := (collarScalar 1 lower inverse).map_smul (annularCellSymbol length mode) h
  exact algebra.trans (congrArg₂ (fun first second : CollarL2 (ComplexEuclidean 1) lower =>
    collarScalar 1 lower radial (collarScalar 1 lower inverse q) +
      collarScalar 1 lower potential (collarScalar 1 lower inverse u) -
      (4 : ℝ) • collarScalar 1 lower radial (collarScalar 1 lower radial (collarScalar 1 lower inverse u)) - first - second)
    mappedG mappedH)

/-- The retained second row multiplied by its nonzero high-sector D symbol.
Together with D p=-q and the genuine p weak graph, this is the original
second equation without a division by the cell frequency. -/
theorem annularPhysical_second_row_D (bounded : lower ≤ 1)
    (field : annularEnergySpace lower length positive) (source : AnnularForcing lower) (mode : HighAnnularMode) :
    let p := annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode
    let xi := annularPhysicalValue parameters lower length positive bounded mode field
    annularDSymbol mode • annularPhysicalPSlope parameters lower length positive lengthPositive widthHalf widthLength bounded field source mode -
      collarScalar 1 lower (annularInverseRadiusCurve lower positive) (annularDSymbol mode • p) +
      collarScalar 1 lower (annularPotentialCurve lower length positive mode) xi -
      (4 : ℝ) • collarScalar 1 lower (annularInverseRadiusCurve lower positive)
        (collarScalar 1 lower (annularInverseRadiusCurve lower positive) xi) =
      annularDSymbol mode • annularDecodeMode parameters lower positive mode (source.2.1 mode) +
      annularCellSymbol length mode • annularDecodeMode parameters lower positive mode (source.2.2.1 mode) := by
  dsimp only
  unfold annularPhysicalPSlope
  rw [smul_smul, mul_neg, mul_inv_cancel₀ (annularDSymbol_ne_zero mode), neg_one_smul,
    annularPhysicalP_D parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode,
    map_neg, annularPhysicalQSlope_formula parameters lower length positive lengthPositive widthHalf widthLength bounded field source mode]
  abel

end SecondRow
end Grad.AnnularReconstruction
