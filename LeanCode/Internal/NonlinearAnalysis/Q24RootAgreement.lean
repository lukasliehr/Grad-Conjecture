import Q8OperatorMajorants

noncomputable section

open scoped BigOperators

namespace Grad.Q8FixedGrade

open Grad.CartesianState Grad.NonlinearQuotientBounds

theorem seriesMajorant_tail {parameters : PhaseParameters}
    {terms : ℕ → TameCoefficient parameters} {majorant : ℕ → ℕ → ℝ}
    (major : SeriesMajorant terms majorant) (start : ℕ) :
    SeriesMajorant (fun p => terms (p + start)) (fun grade p => majorant grade (p + start)) :=
  fun grade => ⟨fun p => (major grade).1 (p + start), (summable_nat_add_iff start).2 (major grade).2⟩

theorem tameSeries_eq_partial_add_tail {parameters : PhaseParameters}
    (terms : ℕ → TameCoefficient parameters) {majorant : ℕ → ℕ → ℝ}
    (major : SeriesMajorant terms majorant) (start : ℕ) :
    tameSeries terms major = (∑ p ∈ Finset.range start, terms p) +
      tameSeries (fun p => terms (p + start)) (seriesMajorant_tail major start) := by
  apply Subtype.ext
  funext cell
  change (∑' p, (terms p).val cell) =
    ((∑ p ∈ Finset.range start, terms p) : TameCoefficient parameters).val cell +
      ∑' p, (terms (p + start)).val cell
  have sumLaw : ((∑ p ∈ Finset.range start, terms p) : TameCoefficient parameters).val cell =
      ∑ p ∈ Finset.range start, (terms p).val cell := by
    simp
  rw [sumLaw]
  exact ((major.value_summable cell).sum_add_tsum_nat_add start).symm

/-- The accepted coefficient-core series converges in every exact fixed-grade
norm, not only coefficientwise. This identifies its Banach realization. -/
theorem embed_tameSeries_hasSum (parameters : PhaseParameters) (grade : ℕ)
    (terms : ℕ → TameCoefficient parameters) {majorant : ℕ → ℕ → ℝ}
    (major : SeriesMajorant terms majorant) :
    HasSum (fun p => embed parameters grade (terms p))
      (embed parameters grade (tameSeries terms major)) := by
  have summableNorm : Summable (fun p => ‖embed parameters grade (terms p)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => by rw [embed_norm]; exact (major grade).1 p) (major grade).2
  have summable := summableNorm.of_norm
  have limit : Filter.Tendsto
      (fun start => ∑ p ∈ Finset.range start, embed parameters grade (terms p))
      Filter.atTop (nhds (embed parameters grade (tameSeries terms major))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ (tendsto_sum_nat_add (majorant grade))
    intro start
    rw [← map_sum, norm_sub_rev, ← map_sub, embed_norm]
    rw [tameSeries_eq_partial_add_tail terms major start, add_sub_cancel_left]
    exact tameSeries_envelope_le _ (seriesMajorant_tail major start) grade
  have equality := tendsto_nhds_unique summable.hasSum.tendsto_sum_nat limit
  exact equality ▸ summable.hasSum

theorem rootSeries_completion_agrees (parameters : PhaseParameters) (grade : ℕ)
    (value : TameCoefficient parameters) (small : coefficientEnvelope 0 value < 1) :
    (∑' p, coefficientTerm p (embed parameters grade value)) =
      embed parameters grade (rootSeries value small) := by
  have converges := embed_tameSeries_hasSum parameters grade
    (fun p => ((rootDerivativeCoefficient 0 p : ℝ) : ℂ) • value ^ p)
    (rootSeriesMajorant_is_majorant 0 small)
  have terms : (fun p => embed parameters grade
        (((rootDerivativeCoefficient 0 p : ℝ) : ℂ) • value ^ p)) =
      fun p => coefficientTerm p (embed parameters grade value) := by
    funext p
    rw [coefficientTerm_embed]
    simp [rootDerivativeCoefficient]
  rw [terms] at converges
  exact converges.tsum_eq

end Grad.Q8FixedGrade
