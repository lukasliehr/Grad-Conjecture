import MP1BridgeRepresentative

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers

namespace Grad.Mollifier.Pointwise.Bridge

universe valueUniverse

def univToVolume (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] : DomainL2 Value Set.univ →ₗᵢ[ℂ] VolumeL2 Value :=
  Lp.compMeasurePreservingₗᵢ ℂ id
    (by simpa only [Measure.restrict_univ] using MeasurePreserving.id (volume : Measure Spatial))

theorem univToVolume_ae (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] (field : DomainL2 Value Set.univ) :
    univToVolume Value field =ᵐ[volume] field :=
  Lp.coeFn_compMeasurePreserving field _

theorem translationSpecializationGoal : TranslationSpecializationGoal := by
  intro Value _normed _inner _complete kernel integrableKernel field integrableFamily translated
  let identification := univToVolume Value
  let family : Spatial → VolumeL2 Value := fun offset =>
    identification (kernel offset • Grad.SpatialTranslation.translation Value offset field)
  let representative : Spatial → Spatial → Value := fun offset point =>
    kernel offset • field (point - offset)
  have integrableIdentified : Integrable family volume :=
    identification.toContinuousLinearMap.integrable_comp integrableFamily
  have jointlyMeasurable : AEStronglyMeasurable (Function.uncurry representative)
      ((volume : Measure Spatial).prod volume) := by
    have measurableField : AEStronglyMeasurable (field : Spatial → Value) volume := by
      simpa only [Measure.restrict_univ] using Lp.aestronglyMeasurable field
    exact (integrableKernel.aestronglyMeasurable.convolution_integrand
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Value →L[ℝ] Value) measurableField).prod_swap
  have represented : ∀ᵐ offset ∂(volume : Measure Spatial),
      family offset =ᵐ[volume] representative offset := by
    apply Filter.Eventually.of_forall
    intro offset
    have scaled : (kernel offset • Grad.SpatialTranslation.translation Value offset field)
        =ᵐ[volume] (fun point => kernel offset •
          Grad.SpatialTranslation.translation Value offset field point) := by
      exact ae_mono (by simp : (volume : Measure Spatial) ≤ volume.restrict Set.univ)
        (Lp.coeFn_smul (kernel offset) (Grad.SpatialTranslation.translation Value offset field))
    exact (univToVolume_ae Value _).trans
      (scaled.trans ((translated offset).fun_comp (fun value => kernel offset • value)))
  have realization := lpIntegralRepresentativeGoal Value Spatial volume family representative
    integrableIdentified jointlyMeasurable represented
  have convolutionEquality : (fun point => ∫ offset, representative offset point) =
      smoothRepresentative Value kernel field := by
    exact (MeasureTheory.convolution_flip
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Value →L[ℝ] Value)
      (f := kernel) (g := (field : Spatial → Value)) (μ := volume)).symm
  have integralIdentification : (∫ offset, family offset) =
      identification (Grad.SpatialTranslation.average Value kernel field) :=
    identification.integral_comp_comm _
  have averageEquality : Grad.SpatialTranslation.average Value kernel field =ᵐ[volume]
      smoothRepresentative Value kernel field := by
    refine (univToVolume_ae Value _).symm.trans ?_
    change identification (Grad.SpatialTranslation.average Value kernel field) =ᵐ[volume] _
    rw [← integralIdentification, ← convolutionEquality]
    exact realization.2.1
  exact ⟨averageEquality, convolutionEquality ▸ realization.2.2⟩

theorem blockGoal : BlockGoal :=
  ⟨finiteSetIntegralGoal, localProductGoal, localFubiniGoal,
    lpIntegralRepresentativeGoal, translationSpecializationGoal⟩

end Grad.Mollifier.Pointwise.Bridge
