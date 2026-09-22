import BanachCalcSeriesProof

/-!
# Goal-only consumers of NG_F04 and NG_F05

Both consumers take the public goals as hypotheses and never unfold a proof.

* `operatorSeries_contDiffOn` (the NG_F05 consumer gate "induct to ordinary
  ContDiff of the coefficient series; no merely directional derivative
  claim"): the coefficient series `x ↦ ∑' p, F p x` is `C^∞` on `U`, and its
  `j`-th Fréchet derivative at every point of `U` is the operator-series sum
  `operatorSeriesSum F j`. The induction over orders is packaged as a
  `HasFTaylorSeriesUpToOn ∞` witness whose order-`j` term is `G_j`: order zero
  is the series itself (NG_F04 summability), the derivative field is NG_F05,
  and the continuity field is NG_F04.
* `operatorSeries_hasFDerivAt_zero` (NG_F04/NG_F05 at order zero): the
  coefficient series itself has Fréchet derivative `h ↦ G_1(x)[h]` at every
  `x ∈ U`, in the ordinary (not directional) sense.
-/

universe u v

open scoped ContDiff

namespace Grad.FiniteBanachCalculus

/-- NG_F05 consumer gate: the coefficient series is `C^∞` on `U` with iterated
Fréchet derivatives the operator-series sums, obtained from the two goals
through a `HasFTaylorSeriesUpToOn ∞` witness. -/
theorem operatorSeries_contDiffOn (hF04 : OperatorSeriesLimitGoal.{u, v})
    (hF05 : OperatorSeriesDerivativeGoal.{u, v})
    {X : Type u} {Y : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (U : Set X) (F : ℕ → X → Y) (hU : IsOpen U) (hF : ∀ p, ContDiffOn ℝ ∞ (F p) U)
    (hM : HasLocalOperatorMajorants U F) :
    ContDiffOn ℝ ∞ (fun x => ∑' p, F p x) U ∧
      ∀ j : ℕ, ∀ x ∈ U, iteratedFDeriv ℝ j (fun y => ∑' p, F p y) x = operatorSeriesSum F j x := by
  have hT : HasFTaylorSeriesUpToOn ∞ (fun x => ∑' p, F p x)
      (fun x j => operatorSeriesSum F j x) U := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      have hs : Summable fun p => iteratedFDeriv ℝ 0 (F p) x := (hF04 U F hU hF hM 0).1 x hx
      have key := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => X) Y 0).map_tsum hs
      exact key
    · intro m _ x hx
      exact (hF05 U F hU hF hM m x hx).hasFDerivWithinAt
    · intro m _
      exact (hF04 U F hU hF hM m).2.1
  refine ⟨hT.contDiffOn, ?_⟩
  intro j x hx
  have h1 := hT.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := j) (le_of_lt (natCast_lt_infty j))
    hU.uniqueDiffOn hx
  rw [iteratedFDerivWithin_of_isOpen j hU hx] at h1
  exact h1.symm

/-- Order-zero instance of NG_F05 through NG_F04: the coefficient series has an
ordinary Fréchet derivative at every `x ∈ U`, and that derivative applied to a
direction `h` is `G_1(x)[h]` (no merely directional claim). -/
theorem operatorSeries_fderiv_apply (hF04 : OperatorSeriesLimitGoal.{u, v})
    (hF05 : OperatorSeriesDerivativeGoal.{u, v})
    {X : Type u} {Y : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (U : Set X) (F : ℕ → X → Y) (hU : IsOpen U) (hF : ∀ p, ContDiffOn ℝ ∞ (F p) U)
    (hM : HasLocalOperatorMajorants U F) {x : X} (hx : x ∈ U) (h : X) :
    HasFDerivAt (fun y => ∑' p, F p y) (fderiv ℝ (fun y => ∑' p, F p y) x) x ∧
      fderiv ℝ (fun y => ∑' p, F p y) x h = operatorSeriesSum F 1 x (fun _ => h) := by
  obtain ⟨hd, hiter⟩ := operatorSeries_contDiffOn hF04 hF05 U F hU hF hM
  have h1 : DifferentiableAt ℝ (fun y => ∑' p, F p y) x :=
    (hd.contDiffAt (hU.mem_nhds hx)).differentiableAt (natCast_lt_infty 0).ne'
  refine ⟨h1.hasFDerivAt, ?_⟩
  rw [← hiter 1 x hx, iteratedFDeriv_one_apply]

end Grad.FiniteBanachCalculus
