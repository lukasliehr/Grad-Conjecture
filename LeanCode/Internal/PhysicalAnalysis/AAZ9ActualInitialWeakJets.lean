import AAZ8LiteralInitialSlopes

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRadialJets
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem annularSecondRow_rearrange {E : Type*} [AddCommGroup E] (a b c d e : E)
    (row : a - b - c = d + e) : b + c + d + e = a := by
  calc
    _ = b + c + (d + e) := by abel
    _ = b + c + (a - b - c) := congrArg (fun value => b + c + value) row.symm
    _ = a := by abel

theorem annularFirstRow_rearrange {E : Type*} [AddCommGroup E] (a b c d : E)
    (row : a + b + c = d) : -b - c + d = a := by
  calc
    _ = -b - c + (a + b + c) := congrArg (fun value => -b - c + value) row.symm
    _ = a := by abel

def annularOriginalRawSource (lower : ℝ) (source : AnnularForcing lower) : AnnularRawSource lower :=
  (fun mode => source.1 mode, (fun mode => source.2.1 mode, fun mode => source.2.2.1 mode))

section Actual
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

def annularOriginalRawState (source : AnnularForcing lower) (innerValue : AnnularBoundary) : AnnularRawState lower :=
  let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  (fun mode => annularRecoveredP parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode,
    fun mode => annularEnergyValue lower length positive field mode)

/-- The initial step of the recursive jets is derived from the checked
original physical equations and actual weak solution. It is not assumed. -/
theorem annularOriginalRawState_initialWeak (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    let initial := annularOriginalRawState parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
    let forcing := annularOriginalRawSource lower source
    AnnularPhysicalWeakDerivative parameters lower positive initial.1 (annularFirstRawSlope lower positive length initial forcing).1 ∧
    AnnularPhysicalWeakDerivative parameters lower positive initial.2 (annularFirstRawSlope lower positive length initial forcing).2 := by
  dsimp only
  let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  let initial := annularOriginalRawState parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  let forcing := annularOriginalRawSource lower source
  constructor
  · intro mode
    have weak := collarWeak_isCompact 1 lower _ _
      (annularPhysicalP_weak parameters lower length positive lengthPositive widthHalf widthLength bounded source innerValue mode)
    have xiLaw := (annularPhysicalValue_eq_decode parameters lower length positive bounded.le mode field).symm
    have slope := annularFirstSlope_decode parameters lower positive length initial forcing mode
    change annularDecodeMode parameters lower positive mode ((annularFirstRawSlope lower positive length initial forcing).1 mode) =
      annularRadiusPower lower positive 1 (annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode) +
      Complex.I • collarScalar 1 lower (annularSecondRealCurve lower length positive mode)
        (annularDecodeMode parameters lower positive mode (annularEnergyValue lower length positive field mode)) +
      annularDecodeMode parameters lower positive mode (source.2.1 mode) +
      annularLongitudinalSourceSymbol length mode • annularDecodeMode parameters lower positive mode (source.2.2.1 mode) at slope
    rw [xiLaw] at slope
    have row := annularOriginal_second_row parameters lower length positive bounded.le lengthPositive widthHalf widthLength field source mode
    have rearranged := annularSecondRow_rearrange _ _ _ _ _ row
    have target := slope.trans rearranged
    exact (congrArg (CompactWeakDerivative 1 lower
      (annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode)) target).mpr weak
  · intro mode
    have weak := collarWeak_isCompact 1 lower _ _ (annularPhysicalValue_weak parameters lower length positive bounded.le mode field)
    have xiLaw := (annularPhysicalValue_eq_decode parameters lower length positive bounded.le mode field).symm
    have slope : annularDecodeMode parameters lower positive mode ((annularFirstRawSlope lower positive length initial forcing).2 mode) =
        annularPhysicalSlope parameters lower length positive bounded.le mode field := by
      change annularDecodeMode parameters lower positive mode
        ((-2 : ℝ) • annularRadiusPower lower positive 1 (annularEnergyValue lower length positive field mode) +
          (-annularDSymbol mode) • annularRecoveredP parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode + source.1 mode) = _
      rw [map_add, map_add,
        (annularDecodeMode parameters lower positive mode).map_smul_of_tower (-2 : ℝ),
        (annularDecodeMode parameters lower positive mode).map_smul (-annularDSymbol mode),
        annularRadiusPower_decode, xiLaw]
      have row := annularPhysical_first_row parameters lower length positive lengthPositive widthHalf widthLength bounded.le field source.1 mode
      rw [collarScalar_radial_twice] at row
      have rearranged := annularFirstRow_rearrange _ _ _ _ row
      change (-2 : ℝ) • annularRadiusPower lower positive 1
          (annularPhysicalValue parameters lower length positive bounded.le mode field) +
        (-annularDSymbol mode) • annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode +
        annularDecodeMode parameters lower positive mode (source.1 mode) = _
      exact (show _ = _ from by rw [neg_smul, neg_smul, sub_eq_add_neg]; rfl).trans rearranged
    exact (congrArg₂ (CompactWeakDerivative 1 lower) xiLaw slope).mpr weak

end Actual
end Grad.AnnularRadialJets
