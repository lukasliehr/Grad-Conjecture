import ReparametrizationEmbedding

noncomputable section

namespace Grad.MainAssembly.TargetReparametrization.Consumer

open Grad.MainTarget

/-- Immediate full-configuration consumer required by the next target
relation-equivalence boundary. -/
theorem configuration_precomposition
    (regularity : Regularity) (admissible : regularity.admissible)
    (configuration : Representative)
    (configurationRegular : IsConfiguration regularity configuration)
    (reparametrization : Reference ≃ Reference)
    (isReparametrization : IsReparametrization regularity reparametrization) :
    IsConfiguration regularity
      { position := configuration.position ∘ reparametrization
        magnetic := configuration.magnetic ∘ reparametrization
        pressure := configuration.pressure ∘ reparametrization } := by
  refine ⟨isEmbeddingOfRegularity_comp regularity admissible
      configuration.position reparametrization configurationRegular.1
      isReparametrization, ?_, ?_⟩
  · exact predecessorHasRegularity_comp regularity configuration.magnetic
      reparametrization configurationRegular.2.1 isReparametrization
  · exact hasRegularity_comp regularity configuration.pressure
      reparametrization configurationRegular.2.2 isReparametrization

end Grad.MainAssembly.TargetReparametrization.Consumer
