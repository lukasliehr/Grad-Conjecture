import AAR20ActualMomentGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

def annularOuterProfile (lower : ℝ) (radius : ℝ) : ℝ := (radius - lower) / (1 - lower)

theorem annularOuterProfile_smooth (lower : ℝ) : ContDiff ℝ ∞ (annularOuterProfile lower) := by
  unfold annularOuterProfile
  fun_prop

theorem annularOuterProfile_inner (lower : ℝ) : annularOuterProfile lower lower = 0 := by
  simp only [annularOuterProfile, sub_self, zero_div]

theorem annularOuterProfile_outer (lower : ℝ) (bounded : lower < 1) : annularOuterProfile lower 1 = 1 :=
  div_self (by linarith)

theorem sqrtTwo_boundary_pairing (vector value : ComplexEuclidean 1) :
    inner ℂ ((Real.sqrt 2 : ℂ) • vector) ((Real.sqrt 2 : ℂ) • value) =
      inner ℂ vector ((2 : ℝ) • value) := by
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  change (2 : ℂ) * inner ℂ vector value = inner ℂ vector ((2 : ℂ) • value)
  exact (inner_smul_right vector value (2 : ℂ)).symm

section Boundary
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- The natural outer trace of the actual recovered moment, obtained from
free endpoint tests and the genuine radial graph integration by parts. -/
theorem annularQMomentGraph_outer (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) :
    weightedRadialTrace 1 lower positive bounded 1
      (annularQMomentGraph parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode) =
      -((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • source.2.2.2 mode) := by
  let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  let graph := annularUncorrectedMomentGraph parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode
  let profile := annularOuterProfile lower
  let smooth := annularOuterProfile_smooth lower
  apply ext_inner_left ℂ
  intro vector
  have law := annularUncorrectedMoment_boundary_test parameters lower length positive bounded lengthPositive widthHalf widthLength
    source innerValue mode profile smooth (annularOuterProfile_inner lower) vector
  dsimp only at law
  have parts := weightedRadial_endpoint_parts 1 lower positive bounded graph vector profile smooth
  change collarPairing lower _ vector
      (collarH1Coordinate (ComplexEuclidean 1) lower 0
        (weightedToOrdinary 1 lower positive bounded.le
          (compactWeakRadialGraph lower positive bounded _ _ _))) +
    collarPairing lower _ vector
      (collarH1Coordinate (ComplexEuclidean 1) lower 1
        (weightedToOrdinary 1 lower positive bounded.le
          (compactWeakRadialGraph lower positive bounded _ _ _))) = _ at parts
  rw [compactWeakRadialGraph_value, compactWeakRadialGraph_slope] at parts
  have profileInner : profile lower = 0 := annularOuterProfile_inner lower
  have profileOuter : profile 1 = 1 := annularOuterProfile_outer lower bounded
  rw [profileInner, profileOuter,
    zero_smul, one_smul, sub_zero] at parts
  rw [profileOuter, one_smul,
    annularEnergyOuter_eq_trace lower length positive bounded mode field,
    sqrtTwo_boundary_pairing] at law
  have reduced := (congrArg (fun value : ℂ => value +
      inner ℂ vector ((2 : ℝ) • weightedRadialTrace 1 lower positive bounded 1
        (annularModeRadialH1 lower length positive mode field))) parts).symm.trans law
  change inner ℂ vector (weightedRadialTrace 1 lower positive bounded 1
    (graph + (2 : ℝ) • annularModeRadialH1 lower length positive mode field)) = _
  simp only [map_add, map_smul, inner_add_right, inner_neg_right, inner_smul_right,
    inner_smul_left, Complex.conj_ofReal] at reduced ⊢
  exact reduced

end Boundary
end Grad.AnnularReconstruction
