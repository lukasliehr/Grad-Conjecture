import GQC69ExactNormConsumer

noncomputable section

namespace Grad.GaugeCoefficients.Physical.Compensated

section Generic
variable {C E T : Type*} [AddCommGroup C] [Module ℂ C]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup T] [NormedSpace ℂ T] [CompleteSpace T]

/-- The closure of the actual core graph image, with its induced norm. -/
def coreGraphClosure (embed : C →ₗ[ℂ] E) : Submodule ℂ E :=
  (LinearMap.range embed).topologicalClosure

def coreGraphInto (embed : C →ₗ[ℂ] E) : C →ₗ[ℂ] coreGraphClosure embed :=
  embed.codRestrict _ (fun core => Submodule.le_topologicalClosure _ ⟨core, rfl⟩)

theorem coreGraphInto_norm (embed : C →ₗ[ℂ] E) (core : C) :
    ‖coreGraphInto embed core‖ = ‖embed core‖ := rfl

theorem coreGraphInto_denseRange (embed : C →ₗ[ℂ] E) : DenseRange (coreGraphInto embed) := by
  let source := LinearMap.range embed
  let inclusion : source →L[ℂ] coreGraphClosure embed :=
    source.subtypeL.codRestrict _ (fun point => Submodule.le_topologicalClosure _ point.property)
  have dense : DenseRange inclusion := by
    change DenseRange (Set.inclusion (Submodule.le_topologicalClosure source))
    exact (denseRange_inclusion_iff _).2 (fun _ member => member)
  apply dense.mono
  rintro _ ⟨point, rfl⟩
  obtain ⟨core, equality⟩ := point.property
  exact ⟨core, Subtype.ext equality⟩

/-- Extend bounded actual graph data, without adding independent weak
derivative coordinates or declaring a maximal PDE domain. -/
theorem coreGraph_extension (embed : C →ₗ[ℂ] E) (mapping : C →ₗ[ℂ] T)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bound : ∀ core, ‖mapping core‖ ≤ constant * ‖embed core‖) :
    ∃ completed : coreGraphClosure embed →L[ℂ] T,
      (∀ core, completed (coreGraphInto embed core) = mapping core) ∧
      ‖completed‖ ≤ constant := by
  let source := LinearMap.range embed
  have kernel : LinearMap.ker embed ≤ LinearMap.ker mapping := by
    intro core member
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    have bounded := bound core
    rw [LinearMap.mem_ker.mp member, norm_zero, mul_zero] at bounded
    exact le_antisymm bounded (norm_nonneg _)
  let quotient := (LinearMap.ker embed).liftQ mapping kernel
  let rangeMap : source →ₗ[ℂ] T := quotient.comp embed.quotKerEquivRange.symm.toLinearMap
  have rangeLaw (core : C) : rangeMap (embed.rangeRestrict core) = mapping core := by
    have image : embed.quotKerEquivRange (Submodule.Quotient.mk core) = embed.rangeRestrict core :=
      Subtype.ext (LinearMap.quotKerEquivRange_apply_mk embed core)
    change quotient (embed.quotKerEquivRange.symm (embed.rangeRestrict core)) = _
    rw [← image, LinearEquiv.symm_apply_apply]
    exact Submodule.liftQ_apply _ mapping core
  have rangeBound (point : source) : ‖rangeMap point‖ ≤ constant * ‖point‖ := by
    rcases point.property with ⟨core, equality⟩
    have image : embed.rangeRestrict core = point := Subtype.ext equality
    rw [← image, rangeLaw]
    exact bound core
  let continuousCore := rangeMap.mkContinuous constant rangeBound
  let inclusion : source →L[ℂ] coreGraphClosure embed :=
    source.subtypeL.codRestrict _ (fun point => Submodule.le_topologicalClosure source point.property)
  have inclusionDense : DenseRange inclusion := by
    change DenseRange (Set.inclusion (Submodule.le_topologicalClosure source))
    exact (denseRange_inclusion_iff _).2 (fun _ member => member)
  have inclusionIsometry : Isometry inclusion := by intro first second; rfl
  refine ⟨continuousCore.extend inclusion, ?_, ?_⟩
  · intro core
    exact (ContinuousLinearMap.extend_eq continuousCore inclusionDense
      inclusionIsometry.isUniformInducing (embed.rangeRestrict core)).trans (rangeLaw core)
  · have extended := ContinuousLinearMap.opNorm_extend_le continuousCore (N := 1) inclusionDense
      (fun point => by change ‖point‖ ≤ (1 : ℝ) * ‖point‖; simp only [one_mul]; exact le_rfl)
    rw [NNReal.coe_one, one_mul] at extended
    exact extended.trans (LinearMap.mkContinuous_norm_le rangeMap nonnegative rangeBound)

end Generic
end Grad.GaugeCoefficients.Physical.Compensated
