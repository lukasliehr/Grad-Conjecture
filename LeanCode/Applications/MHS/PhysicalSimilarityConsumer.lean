import PhysicalSimilarity
import ModuliCurveAssembly

noncomputable section

namespace Grad.MainAssembly.TargetPhysicalSimilarity.Consumer

open Grad.MainTarget
open Grad.MainAssembly.ModuliCurveAssembly
open Grad.MainAssembly.TargetPhysicalSimilarity

/-- Once the concrete physical construction proves inequivalence under the
exact similarity comparison, every full target `Related` witness cancels. The
same theorem works for every finite or smooth regularity because the reference
map was eliminated by `physicalSimilarity_of_related`. -/
theorem relatedCancellation_of_similarityRigidity
    {interval : Set ℝ} (family : interval → Representative)
    (cellLength : ℝ) (period : ℕ)
    (conclusions : ∀ parameter,
      PhysicalConclusions (family parameter) cellLength period)
    (similarityRigidity : ∀ first second : interval,
      PhysicalSimilarity (family first) (family second) cellLength period →
        first = second)
    (regularity : Regularity) :
    ∀ first second : interval,
      Related regularity
        (⟨family first,
          physicalValidity regularity family cellLength period conclusions first⟩ :
            Configuration regularity)
        (⟨family second,
          physicalValidity regularity family cellLength period conclusions second⟩ :
            Configuration regularity) →
      first = second := by
  intro first second related
  apply similarityRigidity first second
  exact physicalSimilarity_of_related
    (⟨family first,
      physicalValidity regularity family cellLength period conclusions first⟩ :
        Configuration regularity)
    (⟨family second,
      physicalValidity regularity family cellLength period conclusions second⟩ :
        Configuration regularity)
    cellLength period (conclusions first) (conclusions second) related

end Grad.MainAssembly.TargetPhysicalSimilarity.Consumer
