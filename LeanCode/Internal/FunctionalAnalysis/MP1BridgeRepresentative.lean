import MP1BridgeLocal

noncomputable section

open MeasureTheory Grad.PDEBootstrap

namespace Grad.Mollifier.Pointwise.Bridge

theorem lpIntegralRepresentativeGoal : LpIntegralRepresentativeGoal := by
  intro Value _normed _inner _complete Parameter _measurable parameterMeasure _sigma
    family representative integrableFamily jointlyMeasurable represented
  have locallyIntegrableRepresentative : LocallyIntegrable
      (fun point => ∫ parameter, representative parameter point ∂parameterMeasure) volume := by
    apply locallyIntegrable_iff.2
    intro region compactRegion
    exact (localProductGoal Value Parameter parameterMeasure family representative integrableFamily
      jointlyMeasurable represented region compactRegion.measurableSet
      compactRegion.measure_ne_top).integral_prod_right
  have locallyIntegrableIntegral : LocallyIntegrable
      ((∫ parameter, family parameter ∂parameterMeasure) : VolumeL2 Value) volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have integralEquality : ((∫ parameter, family parameter ∂parameterMeasure) : VolumeL2 Value)
      =ᵐ[volume] (fun point => ∫ parameter, representative parameter point ∂parameterMeasure) := by
    have differenceZero := ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'
      (locallyIntegrableIntegral.sub locallyIntegrableRepresentative) (fun region compactRegion => by
        simp only [Pi.sub_apply]
        rw [integral_sub (locallyIntegrableIntegral.integrableOn_isCompact compactRegion)
          (locallyIntegrableRepresentative.integrableOn_isCompact compactRegion)]
        exact sub_eq_zero.2 (localFubiniGoal Value Parameter parameterMeasure family representative
          integrableFamily jointlyMeasurable represented region compactRegion.measurableSet
          compactRegion.measure_ne_top))
    filter_upwards [differenceZero] with point same
    exact sub_eq_zero.1 same
  refine ⟨?_, integralEquality, MemLp.ae_eq integralEquality (Lp.memLp _)⟩
  rw [← (volume : Measure Spatial).restrict_univ, ← iUnion_compactCovering Spatial]
  apply (ae_restrict_iUnion_iff _ _).2
  intro index
  exact (localProductGoal Value Parameter parameterMeasure family representative integrableFamily
    jointlyMeasurable represented (compactCovering Spatial index)
    (isCompact_compactCovering Spatial index).measurableSet
    (isCompact_compactCovering Spatial index).measure_ne_top).prod_left_ae

end Grad.Mollifier.Pointwise.Bridge
