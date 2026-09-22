import AKH1ActualPhaseSlopeJets
import AKC7FiniteOrderIntervalSeries

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open Set
open scoped BigOperators ContDiff
namespace Grad.AnnularWeightedSmoothness

section Jets
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem derivativeTower_iteratedDeriv (jets : ℕ → ℝ → E)
    (derivative : ∀ rank radius, HasDerivAt (jets rank) (jets (rank + 1) radius) radius)
    (rank start : ℕ) : iteratedDeriv rank (jets start) = jets (start + rank) := by
  induction rank with
  | zero => simp
  | succ rank previous =>
      rw [iteratedDeriv_succ, previous]
      funext radius
      simpa only [Nat.add_assoc] using (derivative (start + rank) radius).deriv

theorem derivativeTower_contDiff (jets : ℕ → ℝ → E)
    (derivative : ∀ rank radius, HasDerivAt (jets rank) (jets (rank + 1) radius) radius)
    (order start : ℕ) : ContDiff ℝ order (jets start) := by
  induction order generalizing start with
  | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr (fun radius => (derivative start radius).continuousAt))
  | succ order previous =>
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_hasFDerivAt]
      refine ⟨fun radius => ContinuousLinearMap.toSpanSingleton ℝ (jets (start + 1) radius), ?_, ?_⟩
      · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ E).contDiff :
          ContDiff ℝ order (ContinuousLinearMap.toSpanSingletonLIE ℝ E)).comp (previous (start + 1))
      · intro radius
        exact (derivative start radius).hasFDerivAt

theorem derivativeTower_smooth (jets : ℕ → ℝ → E)
    (derivative : ∀ rank radius, HasDerivAt (jets rank) (jets (rank + 1) radius) radius)
    (start : ℕ) : ContDiff ℝ ∞ (jets start) :=
  contDiff_infty.mpr (fun order => derivativeTower_contDiff jets derivative order start)

theorem iteratedDeriv_real_smul {scalar : ℝ → ℝ} {vector : ℝ → E}
    (rank : ℕ) (radius : ℝ) (one : ContDiff ℝ ∞ scalar) (two : ContDiff ℝ ∞ vector) :
    iteratedDeriv rank (fun point => scalar point • vector point) radius =
      ∑ index ∈ Finset.range (rank + 1),
        rank.choose index • iteratedDeriv index scalar radius • iteratedDeriv (rank - index) vector radius := by
  have product := iteratedDerivWithin_smul (𝕜 := ℝ) (𝔸 := ℝ) (Set.mem_univ radius) uniqueDiffOn_univ
    ((one.of_le (by exact_mod_cast (le_top : (rank : ℕ∞) ≤ ⊤))).contDiffAt.contDiffWithinAt)
    ((two.of_le (by exact_mod_cast (le_top : (rank : ℕ∞) ≤ ⊤))).contDiffAt.contDiffWithinAt)
  simp only [iteratedDerivWithin_univ] at product
  convert product using 1
  congr 1

theorem norm_iteratedDeriv_real_smul_le {scalar : ℝ → ℝ} {vector : ℝ → E}
    (rank : ℕ) (radius : ℝ) (one : ContDiff ℝ ∞ scalar) (two : ContDiff ℝ ∞ vector) :
    ‖iteratedDeriv rank (fun point => scalar point • vector point) radius‖ ≤
      ∑ index ∈ Finset.range (rank + 1),
        (rank.choose index : ℝ) * ‖iteratedDeriv index scalar radius‖ *
          ‖iteratedDeriv (rank - index) vector radius‖ := by
  rw [iteratedDeriv_real_smul rank radius one two]
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro index _
  rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast, norm_smul, mul_assoc]

end Jets
end Grad.AnnularWeightedSmoothness
