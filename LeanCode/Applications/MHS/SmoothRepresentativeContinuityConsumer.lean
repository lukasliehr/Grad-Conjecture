import SmoothRepresentativeContinuity
import ModuliCurveAssembly

noncomputable section

namespace Grad.MainAssembly.SmoothRepresentativeContinuity.Consumer

open Grad.MainTarget
open Grad.MainAssembly.ModuliCurveAssembly
open Grad.MainAssembly.SmoothRepresentativeContinuity

/-- Immediate frozen-target consumer: the exact smooth-family and physical
conclusion fields in `mainTheoremStatement` supply continuity of its dependent
configuration curve at every requested regularity. -/
theorem configurationCurve_of_smoothPhysical
    (lower upper : ℝ) (family : Set.Icc lower upper → Representative)
    (cellLength : ℝ) (period : ℕ)
    (smoothRepresentatives : SmoothRepresentatives (Set.Icc lower upper) family)
    (conclusions : ∀ parameter,
      PhysicalConclusions (family parameter) cellLength period)
    (regularity : Regularity) :
    Continuous (fun parameter =>
      (⟨family parameter,
        physicalValidity regularity family cellLength period conclusions parameter⟩ :
          Configuration regularity)) := by
  exact configurationCurve_continuous_of_smoothRepresentatives
    (Set.Icc lower upper) family smoothRepresentatives regularity
    (physicalValidity regularity family cellLength period conclusions)

end Grad.MainAssembly.SmoothRepresentativeContinuity.Consumer
