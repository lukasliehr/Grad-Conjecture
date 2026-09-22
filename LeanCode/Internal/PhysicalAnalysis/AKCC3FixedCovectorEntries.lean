import AKCC2FixedKernelRepresentatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.RepresentedKernel.SpatialProduct

variable {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {input output : ℕ}
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output)
    (measurable : Measurable coefficient) (integrable : Integrable coefficient measure)

include invariant actionMeasurable measurable integrable

theorem startupFixed_chainFacts (rank : ℕ) (word target : DerivativeIndex rank) :
    Measurable (fun parameter => chainFactor rank (orthogonal parameter) word target) ∧
    ∀ parameter, |chainFactor rank (orthogonal parameter) word target| ≤ 1 :=
  Grad.RepresentedKernel.Composition.Spatial.chainFactors
    (startupFixedRawData measure orthogonal invariant actionMeasurable coefficient measurable integrable)
      rank word target

omit invariant actionMeasurable measurable integrable in
def startupFixedChainCoefficient (rank : ℕ) (word target : DerivativeIndex rank) (parameter : Parameter) : OperatorValue input output :=
  (chainFactor rank (orthogonal parameter) word target : ℂ) • coefficient parameter

theorem startupFixedChainCoefficient_measurable (rank : ℕ) (word target : DerivativeIndex rank) :
    Measurable (startupFixedChainCoefficient orthogonal coefficient rank word target) :=
  (Complex.measurable_ofReal.comp (startupFixed_chainFacts measure orthogonal invariant actionMeasurable coefficient measurable integrable rank word target).1).smul measurable

theorem startupFixedChainCoefficient_norm (rank : ℕ) (word target : DerivativeIndex rank) (parameter : Parameter) :
    ‖startupFixedChainCoefficient orthogonal coefficient rank word target parameter‖ ≤ ‖coefficient parameter‖ := by
  rw [startupFixedChainCoefficient, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right
    ((startupFixed_chainFacts measure orthogonal invariant actionMeasurable coefficient measurable integrable rank word target).2 parameter)
    (norm_nonneg _)).trans_eq (one_mul _)

theorem startupFixedChainCoefficient_integrable (rank : ℕ) (word target : DerivativeIndex rank) :
    Integrable (startupFixedChainCoefficient orthogonal coefficient rank word target) measure := by
  apply integrable.norm.mono'
    (startupFixedChainCoefficient_measurable measure orthogonal invariant actionMeasurable coefficient measurable integrable rank word target).aestronglyMeasurable
  filter_upwards [] with parameter
  exact startupFixedChainCoefficient_norm measure orthogonal invariant actionMeasurable coefficient measurable integrable rank word target parameter

end Grad.CartesianStartup
