import AAR24OriginalSecondSymbols

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

section Original
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- The literal original retained second equation:
p_r - p/r - i(m/r^2+n^2/(m L^2)) xi = G3 + n/(m L) F2.
The only inverse angular symbol is nonzero on |m|>=3; n=0 is included. -/
theorem annularOriginal_second_row (field : annularEnergySpace lower length positive)
    (source : AnnularForcing lower) (mode : HighAnnularMode) :
    annularPhysicalPSlope parameters lower length positive lengthPositive widthHalf widthLength bounded field source mode -
      collarScalar 1 lower (annularInverseRadiusCurve lower positive)
        (annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode) -
      Complex.I • collarScalar 1 lower (annularSecondRealCurve lower length positive mode)
        (annularPhysicalValue parameters lower length positive bounded mode field) =
      annularDecodeMode parameters lower positive mode (source.2.1 mode) +
        (((mode.val.2 : ℝ) / ((mode.val.1 : ℝ) * length) : ℝ) : ℂ) •
          annularDecodeMode parameters lower positive mode (source.2.2.1 mode) := by
  let p := annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode
  let derivative := annularPhysicalPSlope parameters lower length positive lengthPositive widthHalf widthLength bounded field source mode
  let xi := annularPhysicalValue parameters lower length positive bounded mode field
  let radial := collarScalar 1 lower (annularInverseRadiusCurve lower positive)
  let potential := collarScalar 1 lower (annularPotentialCurve lower length positive mode)
  let coefficient := collarScalar 1 lower (annularSecondRealCurve lower length positive mode)
  let g := annularDecodeMode parameters lower positive mode (source.2.1 mode)
  let h := annularDecodeMode parameters lower positive mode (source.2.2.1 mode)
  let ratio : ℂ := (((mode.val.2 : ℝ) / ((mode.val.1 : ℝ) * length) : ℝ) : ℂ)
  have law := annularPhysical_second_row_D parameters lower length positive lengthPositive widthHalf widthLength bounded field source mode
  dsimp only at law
  have zeroth := annularSecondPotential_operator lower length positive lengthPositive mode xi
  change potential xi - (4 : ℝ) • radial (radial xi) = annularDSymbol mode • (-Complex.I • coefficient xi) at zeroth
  apply smul_right_injective (CollarL2 (ComplexEuclidean 1) lower) (annularDSymbol_ne_zero mode)
  change annularDSymbol mode • (derivative - radial p - Complex.I • coefficient xi) =
    annularDSymbol mode • (g + ratio • h)
  rw [smul_sub, smul_sub, smul_add, smul_smul (annularDSymbol mode) ratio,
    annularSecondSource_symbol length lengthPositive mode]
  calc
    _ = annularDSymbol mode • derivative - radial (annularDSymbol mode • p) +
        annularDSymbol mode • (-Complex.I • coefficient xi) := by
      rw [radial.map_smul, neg_smul, smul_neg]
      abel
    _ = annularDSymbol mode • derivative - radial (annularDSymbol mode • p) +
        (potential xi - (4 : ℝ) • radial (radial xi)) :=
      congrArg (fun value : CollarL2 (ComplexEuclidean 1) lower =>
        annularDSymbol mode • derivative - radial (annularDSymbol mode • p) + value) zeroth.symm
    _ = annularDSymbol mode • g + annularCellSymbol length mode • h := by
      calc
        _ = annularDSymbol mode • derivative - radial (annularDSymbol mode • p) +
          potential xi - (4 : ℝ) • radial (radial xi) := by abel
        _ = _ := law

end Original
end Grad.AnnularReconstruction
