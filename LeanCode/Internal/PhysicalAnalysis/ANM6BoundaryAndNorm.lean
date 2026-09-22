import ANM5LiteralRows

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualMeanInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace Grad.CircularHighWeak
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
attribute [local instance] apNormedSpace
variable {L sigma gamma ell : ℝ}

/-- A genuine smooth angular-zero scalar has no actual high trace in AP3. -/
theorem apHighTrace_mean_zero (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 1)
    (mean : ∀ cell, angularClosedJet 0 (apSmoothJet admissible 1 cell field) =
      apSmoothJet admissible 1 cell field) (grade : ℕ) (large : 2 ≤ grade) :
    apHighTrace L sigma gamma ell grade (by omega) (apSmoothGrade L sigma gamma ell 1 grade field) = 0 := by
  apply lp.ext
  funext mode
  have coefficient := apHighTrace_literal admissible large
    (apSmoothGrade L sigma gamma ell 1 grade field) mode
  have trace : apTrace admissible large mode.2 (apSmoothGrade L sigma gamma ell 1 grade field) =
      (apSmoothJet admissible 1 mode.2 field).value :=
    (apSmoothJet_value_trace admissible large field mode.2).symm
  rw [trace, boundaryCoefficient_angular] at coefficient
  have absent : (if 3 ≤ |mode.1| then
      (angularClosedJet mode.1 (apSmoothJet admissible 1 mode.2 field)).value (boundaryDiskPoint 0) else 0) = 0 := by
    split_ifs with high
    · have nonzero : mode.1 ≠ 0 := by intro zero; simp [zero] at high
      have law := angularClosedJet_projection mode.1 0 (apSmoothJet admissible 1 mode.2 field)
      rw [mean mode.2, if_neg nonzero] at law
      rw [law]
      rfl
    · rfl
  have zero := coefficient.trans absent
  have weighted := apBoundary_weighted_coefficient L sigma gamma ell grade
    (apHighTrace L sigma gamma ell grade (by omega) (apSmoothGrade L sigma gamma ell 1 grade field)) mode
  exact weighted.symm.trans ((congrArg (fun value =>
    (apBoundaryWeight L sigma gamma ell grade mode : ℂ) • value) zero).trans (smul_zero _))

theorem meanState_highBoundary (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (raw : IsRawMeanSource admissible source) (grade : ℕ) (large : 1 ≤ grade) :
    circularCoreTrace admissible grade (meanState source) = 0 :=
  apHighTrace_mean_zero admissible
    (apSmoothRadial admissible (compensatedReconstruct admissible (meanState source)))
    (meanState_radial_mean admissible source compatible raw) (grade + 1) (by omega)

theorem quarterValueMap_bound_one : ‖quarterValueMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro value
  exact (quarterValue_norm value).le.trans_eq (one_mul _).symm

private theorem norm_half {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (value : E) :
    ‖(1 / 2 : ℂ) • value‖ = (1 / 2 : ℝ) * ‖value‖ := by
  rw [norm_smul]
  norm_num

theorem meanVector_bound (field : APSmooth L sigma gamma ell 2) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 2 grade (meanVector field)‖ ≤
      (1 / 2 : ℝ) * ‖apSmoothGrade L sigma gamma ell 2 grade field‖ := by
  have turned := (apSmoothValueMap_bound quarterValueMap field grade).trans
    (mul_le_mul_of_nonneg_right quarterValueMap_bound_one (norm_nonneg _))
  have law := map_smul (apSmoothGrade L sigma gamma ell 2 grade) (1 / 2 : ℂ)
    (apSmoothQuarter L sigma gamma ell field)
  exact (congrArg norm law).le.trans ((norm_half _).le.trans
    (mul_le_mul_of_nonneg_left (turned.trans_eq (one_mul _)) (by norm_num)))

private theorem five_squared_zero (a b c d e u v : ℝ)
    (ha : a = 0) (hb : b = u) (hc : c = v) (hd : d = 0) (he : e = 0) :
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = u ^ 2 + v ^ 2 := by
  rw [ha, hb, hc, hd, he]
  ring

/-- Original AN8 five-slot norm, with no derivative loss or width change.
Only the v and Rv slots survive, each at the original source force grade. -/
theorem meanState_norm_bound (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (raw : IsRawMeanSource admissible source) (grade : ℕ) :
    compensatedNorm admissible grade (meanState source) ≤
      ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) source.1‖ := by
  have planar := apPlanar_inclusion admissible (meanVector source.1)
  have scalar := apScalar_inclusion admissible (meanVector source.1)
  have v := congrArg (apSmoothGrade L sigma gamma ell 2 (grade + 1)) planar
  have rv := congrArg (apSmoothGrade L sigma gamma ell 2 (grade + 1))
    ((congrArg (apSmoothRotation admissible 2) planar).trans
      (meanVector_rotation admissible source.1 (meanSource_tangential admissible source compatible raw)))
  have e := (congrArg (apSmoothGrade L sigma gamma ell 1 (grade + 1)) scalar).trans (map_zero _)
  have re := (congrArg (apSmoothGrade L sigma gamma ell 1 (grade + 1))
    ((congrArg (apSmoothRotation admissible 1) scalar).trans (map_zero _))).trans (map_zero _)
  have theta := map_zero (apSmoothGrade L sigma gamma ell 1 (grade + 2))
  have rvNorm : ‖apSmoothGrade L sigma gamma ell 2 (grade + 1)
      (-(1 / 2 : ℂ) • source.1)‖ = (1 / 2 : ℝ) *
      ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) source.1‖ := by
    rw [map_smul, norm_smul]
    norm_num
  have square := (compensatedNorm_sq admissible grade (meanState source)).trans
    (five_squared_zero _ _ _ _ _ _ _
      ((congrArg norm theta).trans norm_zero) (congrArg norm v)
      ((congrArg norm rv).trans rvNorm) ((congrArg norm e).trans norm_zero)
      ((congrArg norm re).trans norm_zero))
  have bound := meanVector_bound source.1 (grade + 1)
  have positive := norm_nonneg (apSmoothGrade L sigma gamma ell 2 (grade + 1) source.1)
  have valuePositive := norm_nonneg (apSmoothGrade L sigma gamma ell 2 (grade + 1) (meanVector source.1))
  have squaredBound := mul_self_le_mul_self valuePositive bound
  have totalPositive := compensatedNorm_nonnegative admissible grade (meanState source)
  nlinarith [sq_nonneg (compensatedNorm admissible grade (meanState source) -
    ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) source.1‖)]

theorem meanState_source_norm_bound (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (raw : IsRawMeanSource admissible source) (grade : ℕ) :
    compensatedNorm admissible grade (meanState source) ≤ ‖capSourceGrade grade source‖ := by
  apply (meanState_norm_bound admissible source compatible raw grade).trans
  have square := capSourceGrade_norm_sq grade source
  have nonnegative := norm_nonneg (capSourceGrade grade source)
  have first := norm_nonneg (apSmoothGrade L sigma gamma ell 2 (grade + 1) source.1)
  nlinarith [sq_nonneg ‖apSmoothGrade L sigma gamma ell 1 grade source.2.1‖,
    sq_nonneg ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) source.2.2‖]

end Grad.ActualMeanInverse
