import Showcase_WithProofs

noncomputable section
open Set
open Grad.MainTarget Grad.Showcase
open scoped ContDiff
namespace Grad.ShowcaseRevisionCheck

/-- The former and shortened theorem conclusions are logically equivalent. -/
theorem main_iff_previous (L : ℝ) :
    (∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 / 2 ∧
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ family : ℕ → Set.Icc a b → Representative,
        ∀ N : ℕ, N₀ ≤ N →
          SmoothFamily (Set.Icc a b) (family N) ∧
          (∀ t : Set.Icc a b, Equilibrium L N (family N t)) ∧
          (∀ k : ℕ, 3 ≤ k → ModuliCurve (.finite k) (Set.Icc a b) (family N)) ∧
          ModuliCurve .smooth (Set.Icc a b) (family N)) ↔
    (∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 / 2 ∧
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧
        ∃ family : ℕ → Set.Icc a b → Representative,
          ∀ N : ℕ, N₀ ≤ N →
            SmoothRepresentatives (Set.Icc a b) (family N) ∧
            (∀ parameter : Set.Icc a b,
              let c := family N parameter
              let Ω := Set.range c.position
              let Γ := roundAxis (N * L)
              IsConfiguration .smooth c ∧
              ∃ (magnetic : Vec → Vec) (pressure : Vec → ℝ),
                SmoothNear Ω magnetic ∧ SmoothNear Ω pressure ∧
                (∀ point : Reference,
                  magnetic (c.position point) = c.magnetic point ∧
                  pressure (c.position point) = c.pressure point) ∧
                -- The unforced MHS equations and the boundary condition.
                (∀ point ∈ interior Ω,
                  cross (magnetic point) (curl magnetic point) + gradient pressure point = 0 ∧
                  divergence magnetic point = 0) ∧
                (∀ point ∈ frontier Ω, TangentTo (frontier Ω) point (magnetic point)) ∧
                -- (i) The round critical axis and nested pressure tori.
                Γ ⊆ interior Ω ∧
                {point | point ∈ Ω ∧ fderiv ℝ pressure point = 0} = Γ ∧
                (∀ value, (pressureLevel Ω pressure value).Nonempty →
                  IsRegularLevel Ω pressure value →
                    IsEmbeddedTorus (pressureLevel Ω pressure value)) ∧
                (∀ point ∈ Ω \ Γ, IsRegularLevel Ω pressure (pressure point)) ∧
                IsPressureFoliation Ω Γ pressure ∧
                -- (ii) The magnetic field vanishes exactly on the axis.
                (∀ point ∈ Ω, magnetic point = 0 ↔ point ∈ Γ) ∧
                -- (iii) The full signed stabilizer is exactly the N rotations.
                (∀ (orthogonal : Vec ≃ₗᵢ[ℝ] Vec) (translation : Vec),
                  SignedStabilizes Ω magnetic pressure orthogonal translation ↔
                  ∃ rotationIndex : ℕ, rotationIndex < N ∧
                    ∀ point : Vec, orthogonal point + translation =
                      rotation (2 * Real.pi * rotationIndex / N) point)) ∧
            -- (iv) Non-isolation, for every finite k ≥ 3 and for C^∞.
            (∀ k : ℕ, 3 ≤ k →
              ModuliCurve (.finite k) (Set.Icc a b) (family N)) ∧
            ModuliCurve .smooth (Set.Icc a b) (family N)) := by
  simp only [Equilibrium, IsMHS, NestedPressureTori, ExactCyclicSymmetry, and_assoc]

#print axioms main_iff_previous
end Grad.ShowcaseRevisionCheck
