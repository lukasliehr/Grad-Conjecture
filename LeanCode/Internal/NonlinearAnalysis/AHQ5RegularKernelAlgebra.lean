import AHQ4NeumannEntryContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.AnnularKernelContinuity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryKernelAction

variable {X : Type*} [TopologicalSpace X] {src mid tgt : ℕ} {parameters : X → PhaseParameters}

/-- Continuity and uniform moment bounds on the actual kernel entries.
This property is proved for the physical generators and closed under their
existing algebra; it does not replace the original kernel or its norm. -/
def RegularKernelFamily (kernel : (x : X) → FullTwoFrequencyKernel (parameters x) src tgt) : Prop :=
  (∀ shift input, Continuous (fun x => (kernel x).entry shift input)) ∧
  ∀ moment, ∃ bound : ℝ, 0 ≤ bound ∧ ∀ x, fullKernelMoment (parameters x) moment (kernel x) ≤ bound

theorem regularKernelFamily_of_bound
    (kernel : (x : X) → FullTwoFrequencyKernel (parameters x) src tgt)
    (entries : ∀ shift input, Continuous (fun x => (kernel x).entry shift input))
    (bound : ℕ → ℝ) (bounded : ∀ moment x, fullKernelMoment (parameters x) moment (kernel x) ≤ bound moment) :
    RegularKernelFamily kernel := by
  refine ⟨entries, fun moment => ⟨max (bound moment) 0, le_max_right _ _, fun x => ?_⟩⟩
  exact (bounded moment x).trans (le_max_left _ _)

theorem RegularKernelFamily.add
    {first second : (x : X) → FullTwoFrequencyKernel (parameters x) src tgt}
    (one : RegularKernelFamily first) (two : RegularKernelFamily second) :
    RegularKernelFamily (fun x => fullKernelAdd (first x) (second x)) := by
  refine ⟨fun shift input => (one.1 shift input).add (two.1 shift input), ?_⟩
  intro moment
  obtain ⟨A, A0, a⟩ := one.2 moment
  obtain ⟨B, B0, b⟩ := two.2 moment
  exact ⟨A + B, add_nonneg A0 B0, fun x =>
    (fullKernelAdd_moment_le (parameters x) moment (first x) (second x)).trans (add_le_add (a x) (b x))⟩

theorem RegularKernelFamily.neg
    {kernel : (x : X) → FullTwoFrequencyKernel (parameters x) src tgt}
    (regular : RegularKernelFamily kernel) :
    RegularKernelFamily (fun x => fullKernelNeg (kernel x)) := by
  refine ⟨fun shift input => (regular.1 shift input).neg, ?_⟩
  intro moment
  obtain ⟨A, A0, a⟩ := regular.2 moment
  exact ⟨A, A0, fun x => (fullKernelNeg_moment_le (parameters x) moment (kernel x)).trans (a x)⟩

theorem RegularKernelFamily.sub
    {first second : (x : X) → FullTwoFrequencyKernel (parameters x) src tgt}
    (one : RegularKernelFamily first) (two : RegularKernelFamily second) :
    RegularKernelFamily (fun x => fullKernelSub (first x) (second x)) :=
  one.add two.neg

theorem RegularKernelFamily.comp
    {outer : (x : X) → FullTwoFrequencyKernel (parameters x) mid tgt}
    {inner : (x : X) → FullTwoFrequencyKernel (parameters x) src mid}
    (one : RegularKernelFamily outer) (two : RegularKernelFamily inner) :
    RegularKernelFamily (fun x => fullKernelComposition (outer x) (inner x)) := by
  obtain ⟨A, A0, a⟩ := one.2 0
  obtain ⟨B, B0, b⟩ := two.2 0
  refine ⟨?_, ?_⟩
  · obtain ⟨D, _, d⟩ := two.2 4
    exact fullKernelComposition_continuous parameters outer inner one.1 two.1 A D A0 a d
  · intro moment
    obtain ⟨C, C0, c⟩ := one.2 moment
    obtain ⟨D, D0, d⟩ := two.2 moment
    refine ⟨2 ^ moment * (C * B + A * D), by positivity, fun x => ?_⟩
    apply (fullKernelComposition_moment_le moment (outer x) (inner x)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add
      (mul_le_mul (c x) (b x) (fullKernelMoment_nonnegative _ _ _) C0)
      (mul_le_mul (a x) (d x) (fullKernelMoment_nonnegative _ _ _) A0)

/-- The actual inverse is regular on the SAME low-moment small family. -/
theorem RegularKernelFamily.negativeInverse {dimension : ℕ}
    {kernel : (x : X) → FullTwoFrequencyKernel (parameters x) dimension dimension}
    (regular : RegularKernelFamily kernel)
    (identity : RegularKernelFamily (fun x => fullIdentityKernel (parameters x) dimension))
    (low : ℝ) (low0 : 0 ≤ low) (low1 : low < 1)
    (small : ∀ x, fullKernelMoment (parameters x) 0 (kernel x) ≤ low) :
    RegularKernelFamily (fun x => fullKernelNegativeIdentityInverse (parameters x) (kernel x) low (small x) low1) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨D, _, d⟩ := regular.2 4
    exact fullKernelNegativeIdentityInverse_continuous parameters kernel regular.1 low D low0 low1 small d
  · intro moment
    obtain ⟨I, I0, i⟩ := identity.2 moment
    obtain ⟨A, A0, a⟩ := regular.2 moment
    have C0 : 0 ≤ fullKernelNeumannConstant moment low :=
      tsum_nonneg fun exponent => mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg low0 _)
    refine ⟨I + fullKernelNeumannConstant moment low * A, by positivity, fun x => ?_⟩
    exact (fullKernelNegativeIdentityInverse_moment_le (parameters x) moment (kernel x) low (small x) low1).trans
      (add_le_add (i x) (mul_le_mul_of_nonneg_left (a x) C0))

end Grad.AnnularKernelContinuity
