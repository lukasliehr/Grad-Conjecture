import ModuliTopology

noncomputable section

namespace Grad.MainAssembly.TargetModuliTopology.Consumer

open Grad.MainTarget
open Grad.MainAssembly.TargetModuliTopology

/-- Immediate `ModuliCurve` continuity consumer: any continuous curve in the
literal target configuration topology remains continuous after projection. -/
theorem continuous_moduli_curve
    {Parameter : Type*} [TopologicalSpace Parameter]
    (regularity : Regularity) (family : Parameter → Representative)
    (validity : ∀ parameter, IsConfiguration regularity (family parameter))
    (continuousConfigurations : Continuous
      (fun parameter =>
        (⟨family parameter, validity parameter⟩ : Configuration regularity))) :
    Continuous (fun parameter =>
      moduliClass regularity
        (⟨family parameter, validity parameter⟩ : Configuration regularity)) :=
  (continuous_moduliClass regularity).comp continuousConfigurations

end Grad.MainAssembly.TargetModuliTopology.Consumer
