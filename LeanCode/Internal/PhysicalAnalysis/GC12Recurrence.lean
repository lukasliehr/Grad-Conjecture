import GC12SlotProduct

noncomputable section

open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann.Regularity

/-- Insert the initial value in front of a forcing sequence. -/
def recurrenceSeed (initial : ℝ) (forcing : ℕ → ℝ) : ℕ → ℝ
  | 0 => initial
  | n + 1 => forcing n

@[simp] theorem recurrenceSeed_zero (initial : ℝ) (forcing : ℕ → ℝ) :
    recurrenceSeed initial forcing 0 = initial := rfl

@[simp] theorem recurrenceSeed_succ (initial : ℝ) (forcing : ℕ → ℝ)
    (n : ℕ) :
    recurrenceSeed initial forcing (n + 1) = forcing n := rfl

theorem recurrenceSeed_summable {initial : ℝ} {forcing : ℕ → ℝ}
    (forcingSummable : Summable forcing) :
    Summable (recurrenceSeed initial forcing) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [recurrenceSeed_succ] using forcingSummable

theorem recurrenceSeed_nonnegative {initial : ℝ} {forcing : ℕ → ℝ}
    (initialNonnegative : 0 ≤ initial)
    (forcingNonnegative : ∀ n, 0 ≤ forcing n) :
    ∀ n, 0 ≤ recurrenceSeed initial forcing n := by
  intro n
  cases n with
  | zero => exact initialNonnegative
  | succ n => exact forcingNonnegative n

/-- The exact geometric convolution solving the scalar inequality
`a (n+1) ≤ theta * a n + forcing n`. -/
def recurrenceMajorant (theta initial : ℝ) (forcing : ℕ → ℝ)
    (n : ℕ) : ℝ :=
  ∑ pair ∈ Finset.antidiagonal n,
    theta ^ pair.1 * recurrenceSeed initial forcing pair.2

theorem recurrenceMajorant_zero (theta initial : ℝ) (forcing : ℕ → ℝ) :
    recurrenceMajorant theta initial forcing 0 = initial := by
  simp [recurrenceMajorant]

theorem recurrenceMajorant_succ (theta initial : ℝ) (forcing : ℕ → ℝ)
    (n : ℕ) :
    recurrenceMajorant theta initial forcing (n + 1) =
      theta * recurrenceMajorant theta initial forcing n + forcing n := by
  unfold recurrenceMajorant
  rw [Finset.Nat.sum_antidiagonal_succ]
  simp only [pow_zero, recurrenceSeed_succ, one_mul, pow_succ]
  calc
    forcing n + ∑ pair ∈ Finset.antidiagonal n,
        theta ^ pair.1 * theta * recurrenceSeed initial forcing pair.2 =
      forcing n + theta *
        ∑ pair ∈ Finset.antidiagonal n,
          theta ^ pair.1 * recurrenceSeed initial forcing pair.2 := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro pair _membership
        ring
    _ = theta *
        (∑ pair ∈ Finset.antidiagonal n,
          theta ^ pair.1 * recurrenceSeed initial forcing pair.2) + forcing n := by
      ring

theorem recurrenceMajorant_nonnegative {theta initial : ℝ}
    {forcing : ℕ → ℝ}
    (thetaNonnegative : 0 ≤ theta) (initialNonnegative : 0 ≤ initial)
    (forcingNonnegative : ∀ n, 0 ≤ forcing n) :
    ∀ n, 0 ≤ recurrenceMajorant theta initial forcing n := by
  intro n
  unfold recurrenceMajorant
  apply Finset.sum_nonneg
  intro pair _membership
  exact mul_nonneg (pow_nonneg thetaNonnegative _)
    (recurrenceSeed_nonnegative initialNonnegative forcingNonnegative _)

theorem recurrenceMajorant_summable {theta initial : ℝ}
    {forcing : ℕ → ℝ}
    (thetaNonnegative : 0 ≤ theta) (thetaLt : theta < 1)
    (initialNonnegative : 0 ≤ initial)
    (forcingNonnegative : ∀ n, 0 ≤ forcing n)
    (forcingSummable : Summable forcing) :
    Summable (recurrenceMajorant theta initial forcing) := by
  have geometricSummable := summable_geometric_of_lt_one thetaNonnegative thetaLt
  have seedSummable := recurrenceSeed_summable
    (initial := initial) forcingSummable
  have pairSummable : Summable (fun pair : ℕ × ℕ =>
      theta ^ pair.1 * recurrenceSeed initial forcing pair.2) :=
    geometricSummable.mul_of_nonneg seedSummable
      (fun n => pow_nonneg thetaNonnegative n)
      (recurrenceSeed_nonnegative initialNonnegative forcingNonnegative)
  exact summable_sum_mul_antidiagonal_of_summable_mul pairSummable

/-- A nonnegative scalar sequence dominated by a strict geometric recurrence
is summable whenever the forcing is summable. -/
theorem summable_of_geometric_recurrence {values forcing : ℕ → ℝ}
    {theta : ℝ}
    (valuesNonnegative : ∀ n, 0 ≤ values n)
    (forcingNonnegative : ∀ n, 0 ≤ forcing n)
    (thetaNonnegative : 0 ≤ theta) (thetaLt : theta < 1)
    (forcingSummable : Summable forcing)
    (step : ∀ n, values (n + 1) ≤ theta * values n + forcing n) :
    Summable values := by
  let majorant := recurrenceMajorant theta (values 0) forcing
  have majorantSummable : Summable majorant :=
    recurrenceMajorant_summable thetaNonnegative thetaLt
      (valuesNonnegative 0) forcingNonnegative forcingSummable
  have dominated : ∀ n, values n ≤ majorant n := by
    intro n
    induction n with
    | zero =>
        simpa only [majorant, recurrenceMajorant_zero] using le_rfl
    | succ n inductionHypothesis =>
        calc
          values (n + 1) ≤ theta * values n + forcing n := step n
          _ ≤ theta * majorant n + forcing n := by gcongr
          _ = majorant (n + 1) := by
            symm
            exact recurrenceMajorant_succ theta (values 0) forcing n
  exact Summable.of_nonneg_of_le valuesNonnegative dominated majorantSummable

end Grad.GaugeCoefficients.Neumann.Regularity
