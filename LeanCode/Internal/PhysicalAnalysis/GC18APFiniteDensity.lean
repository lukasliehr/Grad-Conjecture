import GC18APFiniteCore

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

def apFiniteInto {dimension grade : ℕ} (L sigma gamma ell : ℝ) :
    (ℤ →₀ ClosedJet dimension) →ₗ[ℂ] apGrade L sigma gamma ell dimension grade :=
  (apFiniteEmbed L sigma gamma ell).codRestrict _ (fun field =>
    Submodule.le_topologicalClosure _ ((apFiniteEmbed_range L sigma gamma ell) ▸
      (show apFiniteEmbed L sigma gamma ell field ∈ LinearMap.range (apFiniteEmbed L sigma gamma ell) from ⟨field, rfl⟩)))

theorem apFiniteInto_injective {dimension grade : ℕ} (L sigma gamma ell : ℝ) :
    Function.Injective (apFiniteInto (dimension := dimension) (grade := grade) L sigma gamma ell) := by
  intro first second equality
  exact apFiniteEmbed_injective L sigma gamma ell (congrArg Subtype.val equality)

theorem apFiniteInto_denseRange {dimension grade : ℕ} (L sigma gamma ell : ℝ) :
    DenseRange (apFiniteInto (dimension := dimension) (grade := grade) L sigma gamma ell) := by
  apply (apCoreInclusion_denseRange L sigma gamma ell dimension grade).mono
  rintro _ ⟨core, rfl⟩
  have member : core.val ∈ LinearMap.range (apFiniteEmbed L sigma gamma ell) :=
    (apFiniteEmbed_range L sigma gamma ell).symm ▸ core.property
  rcases member with ⟨field, equality⟩
  exact ⟨field, Subtype.ext equality⟩

def apFiniteJetMap {inputDimension outputDimension : ℕ}
    (mapping : ClosedJet inputDimension →ₗ[ℂ] ClosedJet outputDimension) :
    (ℤ →₀ ClosedJet inputDimension) →ₗ[ℂ] (ℤ →₀ ClosedJet outputDimension) :=
  Finsupp.mapRange.linearMap mapping

theorem apFiniteJetMap_apply {inputDimension outputDimension : ℕ}
    (mapping : ClosedJet inputDimension →ₗ[ℂ] ClosedJet outputDimension)
    (field : ℤ →₀ ClosedJet inputDimension) (cell : ℤ) :
    apFiniteJetMap mapping field cell = mapping (field cell) := rfl

theorem apFiniteJetMap_bound {inputDimension outputDimension grade : ℕ} (L sigma gamma ell : ℝ)
    (mapping : ClosedJet inputDimension →ₗ[ℂ] ClosedJet outputDimension) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell field, ‖apRowLinear (grade := grade) L sigma gamma ell cell (mapping field)‖ ≤
      constant * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖)
    (field : ℤ →₀ ClosedJet inputDimension) :
    ‖apFiniteInto (grade := grade) L sigma gamma ell (apFiniteJetMap mapping field)‖ ≤
      constant * ‖apFiniteInto (grade := grade) L sigma gamma ell field‖ := by
  change ‖apFiniteEmbed (grade := grade) L sigma gamma ell (apFiniteJetMap mapping field)‖ ≤
    constant * ‖apFiniteEmbed (grade := grade) L sigma gamma ell field‖
  calc
    _ ≤ ‖(constant : ℂ) • apFiniteEmbed (grade := grade) L sigma gamma ell field‖ := by
      apply lp.norm_mono (by norm_num)
      intro cell
      rw [apFiniteEmbed_apply, apFiniteJetMap_apply]
      change _ ≤ ‖(constant : ℂ) • apFiniteEmbed (grade := grade) L sigma gamma ell field cell‖
      rw [apFiniteEmbed_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg nonnegative]
      exact bounded cell (field cell)
    _ = _ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg nonnegative]

end Grad.GaugeCoefficients.Physical.RadialLedger
