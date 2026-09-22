import WT1Proof
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

noncomputable section

open MeasureTheory Grad.PDEBootstrap Function
open scoped ContDiff

namespace Grad.WeakTesting.Separation

def coordinateMap (dimension : ℕ) (cell : ℤ) (coordinate : Fin dimension) :
    Cells dimension →L[ℂ] ℂ :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin dimension => ℂ) coordinate ∘L
    lp.evalCLM ℂ (fun _ : ℤ => Values dimension) 2 cell

def SeparationGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ field : Fields dimension domain,
      (∀ (cell : ℤ) (vector : Values dimension) (test : Spatial → ℝ)
        (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test),
        tsupport test ⊆ domain →
          compactPairing dimension domain cell vector test smoothness compactSupport field = 0) →
      field = 0

def EqualityGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ first second : Fields dimension domain,
      (∀ (cell : ℤ) (vector : Values dimension) (test : Spatial → ℝ)
        (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test),
        tsupport test ⊆ domain →
          compactPairing dimension domain cell vector test smoothness compactSupport first =
            compactPairing dimension domain cell vector test smoothness compactSupport second) →
      first = second

def RepresentativeGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ (first second : Spatial → Cells dimension),
      MemLp first 2 (volume.restrict domain) → MemLp second 2 (volume.restrict domain) →
      (∀ (cell : ℤ) (vector : Values dimension) (test : Spatial → ℝ),
        ContDiff ℝ ∞ test → HasCompactSupport test → tsupport test ⊆ domain →
          (∫ point in domain, test point • inner ℂ vector (first point cell)) =
            ∫ point in domain, test point • inner ℂ vector (second point cell)) →
      first =ᵐ[volume.restrict domain] second

theorem separationInterfaceConsumer (separation : SeparationGoal) :
    ∀ (dimension : ℕ) (domain : Set Spatial), IsOpen domain →
      ∀ field : Lp (lp (fun _ : ℤ => EuclideanSpace ℂ (Fin dimension)) 2) 2
          (volume.restrict domain),
        (∀ (cell : ℤ) (vector : EuclideanSpace ℂ (Fin dimension)) (test : Spatial → ℝ)
          (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test),
          tsupport test ⊆ domain →
            compactPairing dimension domain cell vector test smoothness compactSupport field = 0) →
        field = 0 := separation

theorem equalityInterfaceConsumer (equality : EqualityGoal) :
    ∀ (dimension : ℕ) (domain : Set Spatial), IsOpen domain →
      ∀ first second : Lp (lp (fun _ : ℤ => EuclideanSpace ℂ (Fin dimension)) 2) 2
          (volume.restrict domain),
        (∀ (cell : ℤ) (vector : EuclideanSpace ℂ (Fin dimension)) (test : Spatial → ℝ)
          (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test),
          tsupport test ⊆ domain →
            compactPairing dimension domain cell vector test smoothness compactSupport first =
              compactPairing dimension domain cell vector test smoothness compactSupport second) →
        first = second := equality

theorem representativeInterfaceConsumer (uniqueness : RepresentativeGoal) :
    ∀ (dimension : ℕ) (domain : Set Spatial), IsOpen domain →
      ∀ first second : Spatial → lp (fun _ : ℤ => EuclideanSpace ℂ (Fin dimension)) 2,
        MemLp first 2 (volume.restrict domain) → MemLp second 2 (volume.restrict domain) →
        (∀ (cell : ℤ) (vector : EuclideanSpace ℂ (Fin dimension)) (test : Spatial → ℝ),
          ContDiff ℝ ∞ test → HasCompactSupport test → tsupport test ⊆ domain →
            (∫ point in domain, test point • inner ℂ vector (first point cell)) =
              ∫ point in domain, test point • inner ℂ vector (second point cell)) →
        first =ᵐ[volume.restrict domain] second := uniqueness

end Grad.WeakTesting.Separation
