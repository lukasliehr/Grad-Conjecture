import AKO7FullMovingIncomingLogBound
import AKO10CofinalCollarLogIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace Grad.AnnularIncomingIntegrability
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse

/-- Uniform actual retained norms, with the SAME inserted-grade witness and
actual incoming density on each cofinal collar, imply global logarithmic
integrability. No trace or integral estimate is assumed. -/
theorem actualRetainedFamily_logarithmicIntegral_bound
    (upper length : ℝ) (upperBounded : upper ≤ 1) (lengthPositive : 0 < length)
    (collars : ℕ → ℝ) (positive : ∀ index, 0 < collars index) (bounded : ∀ index, collars index < 1)
    (decreasing : Antitone collars) (cofinal : Tendsto collars atTop (𝓝 0))
    (fields weighted : ∀ index, CoupledSpace (collars index) length (positive index) lengthPositive)
    (inserted : ∀ index, CoupledInsertedGrade (collars index) length (positive index) lengthPositive 1 (fields index) (weighted index))
    (density : ℝ → ℝ≥0∞)
    (same : ∀ index, ∀ᵐ radius ∂volume.restrict (Icc (collars index) upper),
      density radius = coupledIncomingSquare (collars index) length (positive index) (bounded index) lengthPositive (fields index) radius)
    (retainedBound insertedBound : ℝ)
    (retained : ∀ index, ‖fields index‖ ≤ retainedBound)
    (insertedNorm : ∀ index, ‖weighted index‖ ≤ insertedBound) :
    (∫⁻ radius, ENNReal.ofReal radius⁻¹ * density radius ∂volume.restrict (Ioc 0 upper)) ≤
      ENNReal.ofReal (insertedBound ^ 2 + retainedBound ^ 2) := by
  apply logarithmicIntegral_bound_of_cofinal_collars upper collars positive decreasing cofinal
  intro index
  have actual := coupledIncomingSquare_log_bound (collars index) length (positive index) (bounded index)
    lengthPositive (fields index) (weighted index) (inserted index)
  have included : Icc (collars index) upper ⊆ Icc (collars index) (1 : ℝ) :=
    fun _ inside => ⟨inside.1,inside.2.trans upperBounded⟩
  have restricted :
      (∫⁻ radius, ENNReal.ofReal radius⁻¹ * coupledIncomingSquare (collars index) length (positive index)
          (bounded index) lengthPositive (fields index) radius ∂volume.restrict (Icc (collars index) upper)) ≤
      ENNReal.ofReal (‖weighted index‖ ^ 2 + ‖fields index‖ ^ 2) :=
    (lintegral_mono' (Measure.restrict_mono included le_rfl) le_rfl).trans actual
  have equality : (∫⁻ radius, ENNReal.ofReal radius⁻¹ * density radius ∂volume.restrict (Icc (collars index) upper)) =
      ∫⁻ radius, ENNReal.ofReal radius⁻¹ * coupledIncomingSquare (collars index) length (positive index)
        (bounded index) lengthPositive (fields index) radius ∂volume.restrict (Icc (collars index) upper) := by
    apply lintegral_congr_ae
    filter_upwards [same index] with radius equality
    exact congrArg (fun value => ENNReal.ofReal radius⁻¹ * value) equality
  have weightedSquare := (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (insertedNorm index))).mpr (insertedNorm index)
  have retainedSquare := (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (retained index))).mpr (retained index)
  exact equality.le.trans (restricted.trans (ENNReal.ofReal_le_ofReal (add_le_add weightedSquare retainedSquare)))

/-- The exact exhaustion consumer: SAME physical incoming values and actual
uniform retained/inserted bounds produce one common vanishing sequence. -/
theorem actualRetainedFamily_common_vanishing_radii
    (upper length : ℝ) (upperPositive : 0 < upper) (upperBounded : upper ≤ 1) (lengthPositive : 0 < length)
    (collars : ℕ → ℝ) (positive : ∀ index, 0 < collars index) (bounded : ∀ index, collars index < 1)
    (decreasing : Antitone collars) (cofinal : Tendsto collars atTop (𝓝 0))
    (fields weighted : ∀ index, CoupledSpace (collars index) length (positive index) lengthPositive)
    (inserted : ∀ index, CoupledInsertedGrade (collars index) length (positive index) lengthPositive 1 (fields index) (weighted index))
    (incoming : ℝ → ℝ) (measurable : Measurable incoming)
    (nonnegative : ∀ radius ∈ Ioc 0 upper, 0 ≤ incoming radius)
    (same : ∀ index, ∀ᵐ radius ∂volume.restrict (Icc (collars index) upper),
      ENNReal.ofReal (incoming radius ^ 2) =
        coupledIncomingSquare (collars index) length (positive index) (bounded index) lengthPositive (fields index) radius)
    (retainedBound insertedBound : ℝ)
    (retained : ∀ index, ‖fields index‖ ≤ retainedBound)
    (insertedNorm : ∀ index, ‖weighted index‖ ≤ insertedBound)
    (exceptional : Set ℝ) (null : volume exceptional = 0) :
    ∃ radii : ℕ → ℝ,
      (∀ index, radii index ∈ Ioc 0 upper) ∧
      (∀ index, radii index ∉ exceptional) ∧
      (∀ index, radii (index + 1) < radii index / 2) ∧
      StrictAnti radii ∧
      (∀ index, incoming (radii index) < 1 / ((index : ℝ) + 1)) ∧
      Tendsto radii atTop (𝓝 0) ∧
      Tendsto (incoming ∘ radii) atTop (𝓝 0) := by
  apply exists_common_vanishing_incoming_radii upper upperPositive incoming measurable nonnegative _ exceptional null
  have global := actualRetainedFamily_logarithmicIntegral_bound upper length upperBounded lengthPositive collars positive bounded
    decreasing cofinal fields weighted inserted (fun radius => ENNReal.ofReal (incoming radius ^ 2)) same
    retainedBound insertedBound retained insertedNorm
  have identity : (∫⁻ radius, ENNReal.ofReal (radius⁻¹ * incoming radius ^ 2) ∂volume.restrict (Ioc 0 upper)) =
      ∫⁻ radius, ENNReal.ofReal radius⁻¹ * ENNReal.ofReal (incoming radius ^ 2) ∂volume.restrict (Ioc 0 upper) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
    exact ENNReal.ofReal_mul (inv_nonneg.mpr inside.1.le)
  exact identity.le.trans_lt (global.trans_lt ENNReal.ofReal_lt_top)

end Grad.AnnularIncomingIntegrability
