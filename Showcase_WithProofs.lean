import AKEH11ExactOriginalMain
import RelatedEquivalence

noncomputable section

-- Paper-facing names for the unchanged definitions in the verified library.
namespace Grad.MainTarget
abbrev PeriodicCircle := CellCircle
abbrev ReferenceDomain := Reference
abbrev ModuliEquivalent := Related
abbrev ModuliSpace := Moduli
abbrev SmoothFamily := SmoothRepresentatives
end Grad.MainTarget

open Set
open scoped ContDiff
namespace Grad.Showcase
open Grad.MainTarget

/-! ## 5. The conditions and the main theorem
These definitions collect the paper's clauses without adding hypotheses. -/
/-- Unforced MHS equations and B tangent to the boundary. -/
def IsMHS (Ω : Set Vec) (B : Vec → Vec) (P : Vec → ℝ) : Prop :=
  (∀ x ∈ interior Ω, cross (B x) (curl B x) + gradient P x = 0 ∧ divergence B x = 0) ∧
  ∀ x ∈ frontier Ω, TangentTo (frontier Ω) x (B x)

/-- (i) The entire critical set is Γ; regular pressure tori fill Ω ∖ Γ. -/
def NestedPressureTori (Ω Γ : Set Vec) (P : Vec → ℝ) : Prop :=
  Γ ⊆ interior Ω ∧ {x | x ∈ Ω ∧ fderiv ℝ P x = 0} = Γ ∧
    (∀ p, (pressureLevel Ω P p).Nonempty → IsRegularLevel Ω P p →
      IsEmbeddedTorus (pressureLevel Ω P p)) ∧
    (∀ x ∈ Ω \ Γ, IsRegularLevel Ω P (P x)) ∧ IsPressureFoliation Ω Γ P

/-- (iii) The full signed stabilizer consists of exactly the N axial rotations. -/
def ExactCyclicSymmetry (N : ℕ) (Ω : Set Vec) (B : Vec → Vec) (P : Vec → ℝ) : Prop :=
  ∀ (O : Vec ≃ₗᵢ[ℝ] Vec) (c : Vec), SignedStabilizes Ω B P O c ↔
    ∃ j : ℕ, j < N ∧ ∀ x : Vec, O x + c = rotation (2 * Real.pi * j / N) x

/-- All fixed-parameter conclusions: a smooth embedded MHS equilibrium
with properties (i)–(iii), not merely a solution of the MHS equations. Its fields
pull back to the same representative c used in the moduli curve. -/
def Equilibrium (L : ℝ) (N : ℕ) (c : Representative) : Prop :=
  let Ω := Set.range c.position
  let Γ := roundAxis (N * L)
  IsConfiguration .smooth c ∧ ∃ (B : Vec → Vec) (P : Vec → ℝ),
    SmoothNear Ω B ∧ SmoothNear Ω P ∧
    (∀ q : ReferenceDomain, B (c.position q) = c.magnetic q ∧ P (c.position q) = c.pressure q) ∧
    IsMHS Ω B P ∧ NestedPressureTori Ω Γ P ∧
    (∀ x ∈ Ω, B x = 0 ↔ x ∈ Γ) ∧ -- (ii) Magnetic zero set is exactly the axis.
    ExactCyclicSymmetry N Ω B P

/-- Quotient equality means exactly the full action defined above. -/
theorem same_moduli_class_iff (r : Regularity) (u v : Configuration r) :
    moduliClass r u = moduliClass r v ↔ ModuliEquivalent r u v := by
  exact Grad.MainAssembly.TargetRelation.moduliClass_eq_iff_related r u v

/-- One common interval, threshold, and family work for all sufficiently large
periods and every regularity. Here lambda is the paper's parameter λ.
Natural periods with N₀ ≥ 1 encode the paper's
sufficiently large integers. Clause (iv) is the pair of ModuliCurve conditions. -/
theorem equilibria_with_exact_cyclic_symmetry (L : ℝ) (hL : 0 < L) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 / 2 ∧
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ family : ℕ → Set.Icc a b → Representative,
        ∀ N : ℕ, N₀ ≤ N →
          SmoothFamily (Set.Icc a b) (family N) ∧
          (∀ lambda : Set.Icc a b, Equilibrium L N (family N lambda)) ∧
          (∀ k : ℕ, 3 ≤ k → ModuliCurve (.finite k) (Set.Icc a b) (family N)) ∧
          ModuliCurve .smooth (Set.Icc a b) (family N) := by
  rcases Grad.OriginalMainConsumer.actualOriginal_mainTheorem L hL with
    ⟨ρ, δ, α, a, b, N₀, _, _, _, _, ha, hab, hb, hN₀, family, hfamily⟩
  refine ⟨a, b, ha, hab, hb, N₀, hN₀, family, ?_⟩
  intro N hN
  obtain ⟨hsmooth, hphysical, hmoduli⟩ := hfamily N hN
  refine ⟨hsmooth, ?_, ?_, ?_⟩
  · intro parameter
    rcases hphysical parameter with
      ⟨hc, B, P, hB, hP, hpull, hmhs, htangent, haxis, hcritical,
        hzero, htori, hregular, hfoliation, hsymmetry⟩
    exact ⟨hc, B, P, hB, hP, hpull, ⟨hmhs, htangent⟩,
      ⟨haxis, hcritical, htori, hregular, hfoliation⟩, hzero, hsymmetry⟩
  · intro k hk
    exact hmoduli (.finite k) hk
  · exact hmoduli .smooth trivial


end Grad.Showcase
