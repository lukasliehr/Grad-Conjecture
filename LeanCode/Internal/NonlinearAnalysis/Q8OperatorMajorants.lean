import Q8FixedGradeDerivatives
import MajorantRootSummable
import BanachCalcSeriesConsumer

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.Q8FixedGrade

open Grad.CartesianState Grad.NonlinearQuotientBounds Grad.CoefficientMajorants
open Grad.FiniteBanachCalculus

/-- The Q8 domain uses only the literal low envelope; higher norms are unrestricted. -/
def rootDomain (parameters : PhaseParameters) (grade : ℕ) : Set (Carrier parameters grade) :=
  {value | lowNorm parameters grade value < 1}

theorem rootDomain_isOpen (parameters : PhaseParameters) (grade : ℕ) :
    IsOpen (rootDomain parameters grade) :=
  isOpen_lt (lowerMap parameters (Nat.zero_le grade)).continuous.norm continuous_const

theorem lowNorm_sub_le (parameters : PhaseParameters) (grade : ℕ)
    (first second : Carrier parameters grade) :
    lowNorm parameters grade first ≤ ‖first - second‖ + lowNorm parameters grade second := by
  have difference := lowerMap_norm_le parameters (Nat.zero_le grade) (first - second)
  unfold lowNorm
  calc
    ‖lowerMap parameters (Nat.zero_le grade) first‖ =
        ‖lowerMap parameters (Nat.zero_le grade) (first - second) +
          lowerMap parameters (Nat.zero_le grade) second‖ := by rw [← map_add, sub_add_cancel]
    _ ≤ ‖lowerMap parameters (Nat.zero_le grade) (first - second)‖ +
        ‖lowerMap parameters (Nat.zero_le grade) second‖ := norm_add_le _ _
    _ ≤ _ := add_le_add difference le_rfl

theorem iteratedFDeriv_coefficientTerm_norm_le (parameters : PhaseParameters)
    (grade order p : ℕ) {theta radius : ℝ} (thetaNonneg : 0 ≤ theta)
    (radiusNonneg : 0 ≤ radius) {value : Carrier parameters grade}
    (lowBound : lowNorm parameters grade value ≤ theta) (highBound : ‖value‖ ≤ radius) :
    ‖iteratedFDeriv ℝ order (coefficientTerm p) value‖ ≤
      rootOperatorMajorant parameters grade order theta radius p := by
  apply ContinuousMultilinearMap.opNorm_le_bound
    (rootOperatorMajorant_nonneg parameters grade order thetaNonneg radiusNonneg p)
  intro directions
  rw [iteratedFDeriv_coefficientTerm_real]
  exact derivativeTerm_norm_le_on_ball parameters grade order p lowBound highBound directions

/-- Actual summable operator-norm majorants on every Q8 low-envelope open domain. -/
theorem root_hasLocalOperatorMajorants (parameters : PhaseParameters) (grade : ℕ) :
    HasLocalOperatorMajorants (rootDomain parameters grade) (fun p => coefficientTerm p) := by
  intro base inside order
  change lowNorm parameters grade base < 1 at inside
  let r : ℝ := (1 - lowNorm parameters grade base) / 2
  let theta : ℝ := lowNorm parameters grade base + r
  let radius : ℝ := ‖base‖ + r
  have rPositive : 0 < r := by dsimp [r]; linarith
  have lowNonneg : 0 ≤ lowNorm parameters grade base := norm_nonneg _
  have thetaNonneg : 0 ≤ theta := add_nonneg lowNonneg rPositive.le
  have thetaLt : theta < 1 := by dsimp [theta, r]; linarith
  have radiusNonneg : 0 ≤ radius := add_nonneg (norm_nonneg _) rPositive.le
  have lowBound : ∀ value ∈ Metric.closedBall base r,
      lowNorm parameters grade value ≤ theta := by
    intro value membership
    have difference : ‖value - base‖ ≤ r := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using membership
    exact (lowNorm_sub_le parameters grade value base).trans (by dsimp [theta]; linarith)
  refine ⟨r, rPositive, (fun value membership => (lowBound value membership).trans_lt thetaLt),
    rootOperatorMajorant parameters grade order theta radius,
    rootOperatorMajorant_summable parameters grade order thetaNonneg thetaLt radiusNonneg, ?_⟩
  intro p value membership
  have difference : ‖value - base‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using membership
  have highBound : ‖value‖ ≤ radius := by
    calc
      ‖value‖ = ‖(value - base) + base‖ := by rw [sub_add_cancel]
      _ ≤ ‖value - base‖ + ‖base‖ := norm_add_le _ _
      _ ≤ radius := by dsimp [radius]; linarith
  exact iteratedFDeriv_coefficientTerm_norm_le parameters grade order p thetaNonneg radiusNonneg
    (lowBound value membership) highBound

/-- Exact NG_F04/05 consumer: the literal Q8 coefficient series is C-infinity
on the full low-envelope domain, and every actual derivative is its operator sum. -/
theorem root_series_contDiffOn (parameters : PhaseParameters) (grade : ℕ) :
    ContDiffOn ℝ ∞ (fun value : Carrier parameters grade => ∑' p, coefficientTerm p value)
      (rootDomain parameters grade) ∧
    ∀ order : ℕ, ∀ value ∈ rootDomain parameters grade,
      iteratedFDeriv ℝ order
          (fun point : Carrier parameters grade => ∑' p, coefficientTerm p point) value =
        operatorSeriesSum (fun p => coefficientTerm p) order value := by
  exact operatorSeries_contDiffOn actualOperatorSeriesLimit actualOperatorSeriesDerivative
    (rootDomain parameters grade) (fun p => coefficientTerm p)
    (rootDomain_isOpen parameters grade)
    (fun p => ((coefficientTerm_contDiff parameters grade p).restrict_scalars ℝ).contDiffOn)
    (root_hasLocalOperatorMajorants parameters grade)

end Grad.Q8FixedGrade
