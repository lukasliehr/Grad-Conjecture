import ReparametrizationHomeomorph

noncomputable section

namespace Grad.MainAssembly.TargetReparametrization.Consumer

open Grad.MainTarget

/-- The topological embedding fact consumed by exact target embedding
preservation. -/
theorem reparametrization_isEmbedding
    (regularity : Regularity)
    (reparametrization : Reference ≃ Reference)
    (isReparametrization : IsReparametrization regularity reparametrization) :
    Topology.IsEmbedding (reparametrization : Reference → Reference) :=
  (reparametrizationHomeomorph regularity reparametrization
    isReparametrization).isEmbedding

end Grad.MainAssembly.TargetReparametrization.Consumer
