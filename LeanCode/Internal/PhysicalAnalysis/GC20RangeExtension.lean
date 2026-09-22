import GC20HilbertCore

noncomputable section

namespace Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Bounded data on a possibly noninjective core factor through its actual
graph image, then extend to that image's closure in the original norm. -/
theorem collarRange_extension {C F T : Type*} [AddCommGroup C] [Module ℝ C]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
    (embed : C →ₗ[ℝ] F) (mapping : C →ₗ[ℝ] T) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bound : ∀ core, ‖mapping core‖ ≤ constant * ‖embed core‖) :
    ∃ completed : (LinearMap.range embed).topologicalClosure →L[ℝ] T,
      (∀ core, completed ⟨embed core, Submodule.le_topologicalClosure _ ⟨core, rfl⟩⟩ = mapping core) ∧
      (∀ field, ‖completed field‖ ≤ constant * ‖field‖) := by
  let source := LinearMap.range embed
  let target := source.topologicalClosure
  have kernel : LinearMap.ker embed ≤ LinearMap.ker mapping := by
    intro core member
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    have bounded := bound core
    rw [LinearMap.mem_ker.mp member, norm_zero, mul_zero] at bounded
    exact le_antisymm bounded (norm_nonneg _)
  let quotient := (LinearMap.ker embed).liftQ mapping kernel
  let rangeMap : source →ₗ[ℝ] T := quotient.comp embed.quotKerEquivRange.symm.toLinearMap
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
  let inclusion : source →L[ℝ] target :=
    source.subtypeL.codRestrict target (fun point => Submodule.le_topologicalClosure source point.property)
  have inclusionDense : DenseRange inclusion := by
    change DenseRange (Set.inclusion (Submodule.le_topologicalClosure source))
    exact (denseRange_inclusion_iff _).2 (fun _ member => member)
  have inclusionIsometry : Isometry inclusion := by
    intro first second
    rfl
  let completed := continuousCore.extend inclusion
  refine ⟨completed, ?_, ?_⟩
  · intro core
    exact ContinuousLinearMap.extend_eq continuousCore inclusionDense
      inclusionIsometry.isUniformInducing (embed.rangeRestrict core) |>.trans (rangeLaw core)
  · intro field
    have extended := ContinuousLinearMap.opNorm_extend_le continuousCore (N := 1) inclusionDense
      (fun point => by change ‖point‖ ≤ (1 : ℝ) * ‖point‖; simp only [one_mul]; exact le_rfl)
    rw [NNReal.coe_one, one_mul] at extended
    exact (completed.le_opNorm field).trans (mul_le_mul_of_nonneg_right
      (extended.trans (LinearMap.mkContinuous_norm_le rangeMap nonnegative rangeBound)) (norm_nonneg _))

end Grad.GaugeCoefficients.Physical.WeightedTrace
