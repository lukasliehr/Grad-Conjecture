import AKO9CommonVanishingIncomingRadii

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace Grad.AnnularIncomingIntegrability

/-- Monotone exhaustion of the punctured collar retains the SAME density;
the uniform fixed-collar bound survives without a lower-radius constant. -/
theorem logarithmicIntegral_bound_of_cofinal_collars
    (upper : ℝ) (collars : ℕ → ℝ) (positive : ∀ index, 0 < collars index)
    (decreasing : Antitone collars) (cofinal : Tendsto collars atTop (𝓝 0))
    (density : ℝ → ℝ≥0∞) (bound : ℝ≥0∞)
    (fixed : ∀ index, (∫⁻ radius, ENNReal.ofReal radius⁻¹ * density radius
      ∂volume.restrict (Icc (collars index) upper)) ≤ bound) :
    (∫⁻ radius, ENNReal.ofReal radius⁻¹ * density radius
      ∂volume.restrict (Ioc 0 upper)) ≤ bound := by
  have cover : (⋃ index, Icc (collars index) upper) = Ioc 0 upper := by
    ext radius
    constructor
    · intro member
      obtain ⟨index,inside⟩ := mem_iUnion.mp member
      exact ⟨(positive index).trans_le inside.1,inside.2⟩
    · intro inside
      obtain ⟨index,small⟩ := (cofinal.eventually (gt_mem_nhds inside.1)).exists
      exact mem_iUnion.mpr ⟨index,small.le,inside.2⟩
  have directed : Directed (· ⊆ ·) (fun index => Icc (collars index) upper) := by
    intro first second
    refine ⟨max first second,?_,?_⟩
    · intro radius inside
      exact ⟨(decreasing (le_max_left _ _)).trans inside.1,inside.2⟩
    · intro radius inside
      exact ⟨(decreasing (le_max_right _ _)).trans inside.1,inside.2⟩
  rw [← cover,setLIntegral_iUnion_of_directed _ directed]
  exact iSup_le fixed

/-- The cofinal-collar integral hypothesis is converted directly to the
full common vanishing-radius conclusion, including null-set avoidance. -/
theorem exists_common_radii_of_cofinal_log_bounds
    (upper : ℝ) (upperPositive : 0 < upper)
    (collars : ℕ → ℝ) (positive : ∀ index, 0 < collars index)
    (decreasing : Antitone collars) (cofinal : Tendsto collars atTop (𝓝 0))
    (incoming : ℝ → ℝ) (measurable : Measurable incoming)
    (nonnegative : ∀ radius ∈ Ioc 0 upper, 0 ≤ incoming radius)
    (bound : ℝ≥0∞) (boundFinite : bound < ⊤)
    (fixed : ∀ index, (∫⁻ radius, ENNReal.ofReal radius⁻¹ * ENNReal.ofReal (incoming radius ^ 2)
      ∂volume.restrict (Icc (collars index) upper)) ≤ bound)
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
  have global := logarithmicIntegral_bound_of_cofinal_collars upper collars positive decreasing cofinal
    (fun radius => ENNReal.ofReal (incoming radius ^ 2)) bound fixed
  have identity : (∫⁻ radius, ENNReal.ofReal (radius⁻¹ * incoming radius ^ 2)
      ∂volume.restrict (Ioc 0 upper)) =
      ∫⁻ radius, ENNReal.ofReal radius⁻¹ * ENNReal.ofReal (incoming radius ^ 2)
        ∂volume.restrict (Ioc 0 upper) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
    exact ENNReal.ofReal_mul (inv_nonneg.mpr inside.1.le)
  exact identity.le.trans_lt (global.trans_lt boundFinite)

end Grad.AnnularIncomingIntegrability
