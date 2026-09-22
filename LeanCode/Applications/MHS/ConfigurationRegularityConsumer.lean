import ConfigurationRegularity

noncomputable section

namespace Grad.MainAssembly.ConfigurationRegularity.Consumer

open Grad.MainTarget
open Grad.MainAssembly.ConfigurationRegularity

/-- Immediate exact `ModuliCurve` validity consumer for a family satisfying
the paper's physical conclusions. -/
theorem moduliCurveValidity_of_physicalConclusions
    {interval : Set ℝ} (regularity : Regularity)
    (family : interval → Representative) (cellLength : ℝ) (period : ℕ)
    (conclusions : ∀ parameter,
      PhysicalConclusions (family parameter) cellLength period) :
    ∀ parameter, IsConfiguration regularity (family parameter) := by
  intro parameter
  exact isConfiguration_of_physicalConclusions regularity
    (family parameter) cellLength period (conclusions parameter)

end Grad.MainAssembly.ConfigurationRegularity.Consumer
