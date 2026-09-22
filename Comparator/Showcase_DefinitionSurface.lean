import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Equilibria with exact cyclic symmetry — Theorem 1.1 of Combined2.tex
Only Mathlib is imported. Every additional notion is defined here.
Read the final theorem first, then the definitions of its conditions.
`∀` means “for every”, `∃` means “there exists”, `∧` means “and”, and `↔`
means “if and only if”. The two presentation proofs are omitted with `sorry`;
Showcase_WithProofs.lean proves the same statements using the verified library.
-/
noncomputable section
open Set
open scoped ContDiff
namespace Grad.ShowcaseSurface.MainTarget

/-! ## 1. Reference domain and regularity, including the boundary
The reference solid torus is Q = closed unit disk × ℝ/(2πℤ).
Derivatives are computed in periodic covering coordinates. -/
abbrev Vec := EuclideanSpace ℝ (Fin 3)
abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev PeriodicCircle := AddCircle (2 * Real.pi)
abbrev ClosedDisk := {x : Plane // ‖x‖ ≤ 1}
abbrev ReferenceDomain := ClosedDisk × PeriodicCircle
abbrev Torus := PeriodicCircle × PeriodicCircle

def vector (x y z : ℝ) : Vec := WithLp.toLp 2 ![x, y, z]
def planarPart (x : Vec) : Plane := WithLp.toLp 2 ![x 0, x 1]
def cylinder : Set Vec := {x | ‖planarPart x‖ ≤ 1}
def fundamentalCylinder : Set Vec :=
  {x | x ∈ cylinder ∧ 0 ≤ x 2 ∧ x 2 ≤ 2 * Real.pi}
def quotientPoint (x : Vec) (hx : x ∈ cylinder) : ReferenceDomain :=
  (⟨planarPart x, hx⟩, (x 2 : PeriodicCircle))
def periodicLift {E : Type*} [Zero E] (f : ReferenceDomain → E) (x : Vec) : E := by
  classical
  exact if hx : x ∈ cylinder then f (quotientPoint x hx) else 0

inductive Regularity where
  | finite (k : ℕ) -- C^k
  | smooth        -- C^∞
def Regularity.order : Regularity → ℕ∞ω
  | .finite k => k
  | .smooth => ∞
def Regularity.predecessor : Regularity → Regularity
  | .finite k => .finite (k - 1)
  | .smooth => .smooth
def Regularity.admits (r : Regularity) (j : ℕ) : Prop := (j : ℕ∞ω) ≤ r.order

/-- At every point of S, f agrees with a C^r map on an open neighborhood. -/
def HasLocalExtensions {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r : Regularity) (f : E → F) (S : Set E) : Prop :=
  ∀ x ∈ S, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
    ∃ g : E → F, ContDiffOn ℝ r.order g U ∧ EqOn g f (U ∩ S)

def HasRegularity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : Regularity) (f : ReferenceDomain → E) : Prop :=
  HasLocalExtensions r (periodicLift f) cylinder

def IsEmbeddingOfRegularity (r : Regularity) (X : ReferenceDomain → Vec) : Prop :=
  HasRegularity r X ∧ Topology.IsEmbedding X ∧
    ∀ x ∈ cylinder, Function.Injective (fderivWithin ℝ (periodicLift X) cylinder x)

/-! ## 2. Configurations and the full moduli space
A representative is (X, B ∘ X, P ∘ X). Its regularities are (k, k−1, k).
The topology is uniform convergence of all permitted derivatives on one
compact fundamental cylinder; for smooth maps, every finite order is used. -/
/-- The paper's triple (X, b, p), with b = B ∘ X and p = P ∘ X.
The magnetic and pressure entries are functions on Q, not on physical space. -/
structure Representative where
  position : ReferenceDomain → Vec -- X
  magnetic : ReferenceDomain → Vec -- b = B ∘ X
  pressure : ReferenceDomain → ℝ   -- p = P ∘ X

def IsConfiguration (r : Regularity) (c : Representative) : Prop :=
  IsEmbeddingOfRegularity r c.position ∧
    HasRegularity r.predecessor c.magnetic ∧ HasRegularity r c.pressure
abbrev Configuration (r : Regularity) := {c : Representative // IsConfiguration r c}

def jets {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : Regularity) (f : ReferenceDomain → E) :
    ∀ j : {j : ℕ // r.admits j},
      UniformFun fundamentalCylinder (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => Vec) E) :=
  fun j => UniformFun.ofFun fun x => iteratedFDerivWithin ℝ j.val (periodicLift f) cylinder x
instance configurationTopology (r : Regularity) : TopologicalSpace (Configuration r) :=
  TopologicalSpace.induced (fun c : Configuration r =>
    (jets r c.val.position, jets r.predecessor c.val.magnetic, jets r c.val.pressure)) inferInstance

/-- A reference diffeomorphism has regular local lifts in both directions. -/
def HasRegularLocalLifts (r : Regularity) (Φ : ReferenceDomain → ReferenceDomain) : Prop :=
  ∀ x ∈ cylinder, ∃ U : Set Vec, IsOpen U ∧ x ∈ U ∧
    ∃ F : Vec → Vec, ContDiffOn ℝ r.order F U ∧
      ∀ y ∈ U, ∀ hy : y ∈ cylinder, ∃ hF : F y ∈ cylinder,
        quotientPoint (F y) hF = Φ (quotientPoint y hy)
def IsReparametrization (r : Regularity) (Φ : ReferenceDomain ≃ ReferenceDomain) : Prop :=
  HasRegularLocalLifts r Φ ∧ HasRegularLocalLifts r Φ.symm

/-- The paper's full action: (X,b,p) ↦ (sOX∘Φ+c, κOb∘Φ, κ²p∘Φ+c₀). -/
def ModuliEquivalent (r : Regularity) (u v : Configuration r) : Prop :=
  ∃ (s κ : ℝ) (O : Vec ≃ₗᵢ[ℝ] Vec) (c : Vec) (c₀ : ℝ) (Φ : ReferenceDomain ≃ ReferenceDomain),
    0 < s ∧ κ ≠ 0 ∧ IsReparametrization r Φ ∧ ∀ q : ReferenceDomain,
      v.val.position q = s • O (u.val.position (Φ q)) + c ∧
      v.val.magnetic q = κ • O (u.val.magnetic (Φ q)) ∧
      v.val.pressure q = κ ^ 2 * u.val.pressure (Φ q) + c₀

def ModuliSpace (r : Regularity) := Quot (ModuliEquivalent r)
def moduliClass (r : Regularity) : Configuration r → ModuliSpace r := Quot.mk (ModuliEquivalent r)
instance moduliTopology (r : Regularity) : TopologicalSpace (ModuliSpace r) :=
  TopologicalSpace.coinduced (moduliClass r) inferInstance

/-! ## 3. Euclidean calculus, pressure surfaces, and signed symmetries
Fields are smooth on a neighborhood of the closed body. Boundary tangency
means being the velocity of a smooth curve contained in the boundary. -/
def basisVector (i : Fin 3) : Vec := WithLp.toLp 2 (Pi.single i 1)
def gradient (P : Vec → ℝ) (x : Vec) : Vec :=
  WithLp.toLp 2 fun i => fderiv ℝ P x (basisVector i)
def cross (u v : Vec) : Vec :=
  vector (u 1 * v 2 - u 2 * v 1) (u 2 * v 0 - u 0 * v 2) (u 0 * v 1 - u 1 * v 0)
def curl (B : Vec → Vec) (x : Vec) : Vec :=
  vector ((fderiv ℝ B x (basisVector 1)) 2 - (fderiv ℝ B x (basisVector 2)) 1)
    ((fderiv ℝ B x (basisVector 2)) 0 - (fderiv ℝ B x (basisVector 0)) 2)
    ((fderiv ℝ B x (basisVector 0)) 1 - (fderiv ℝ B x (basisVector 1)) 0)
def divergence (B : Vec → Vec) (x : Vec) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ B x (basisVector i)) i

def SmoothNear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set Vec) (f : Vec → E) : Prop :=
  ∃ U : Set Vec, IsOpen U ∧ Ω ⊆ U ∧ ContDiffOn ℝ ∞ f U
def TangentTo (S : Set Vec) (x v : Vec) : Prop :=
  ∃ γ : ℝ → Vec, ContDiff ℝ ∞ γ ∧ γ 0 = x ∧ (∀ t, γ t ∈ S) ∧ fderiv ℝ γ 0 1 = v

def roundAxis (R : ℝ) : Set Vec :=
  Set.range fun θ : ℝ => vector (R * Real.cos θ) (R * Real.sin θ) 0
def rotation (θ : ℝ) (x : Vec) : Vec :=
  vector (Real.cos θ * x 0 - Real.sin θ * x 1)
    (Real.sin θ * x 0 + Real.cos θ * x 1) (x 2)

/-- All orthogonal motions are tested, with one global sign for B. -/
def SignedStabilizes (Ω : Set Vec) (B : Vec → Vec) (P : Vec → ℝ)
    (O : Vec ≃ₗᵢ[ℝ] Vec) (c : Vec) : Prop :=
  let g := fun x => O x + c
  g '' Ω = Ω ∧ (∀ x ∈ Ω, P (g x) = P x) ∧
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ Ω, B (g x) = σ • O (B x)

def torusLift (X : Torus → Vec) (x : Plane) : Vec :=
  X ((x 0 : PeriodicCircle), (x 1 : PeriodicCircle))
def IsEmbeddedTorus (S : Set Vec) : Prop :=
  ∃ X : Torus → Vec, ContDiff ℝ ∞ (torusLift X) ∧
    Topology.IsEmbedding X ∧ Set.range X = S ∧
    ∀ x : Plane, Function.Injective (fderiv ℝ (torusLift X) x)
def pressureLevel (Ω : Set Vec) (P : Vec → ℝ) (p : ℝ) : Set Vec :=
  {x | x ∈ Ω ∧ P x = p}
def IsRegularLevel (Ω : Set Vec) (P : Vec → ℝ) (p : ℝ) : Prop :=
  ∀ x ∈ pressureLevel Ω P p, fderiv ℝ P x ≠ 0

abbrev FoliationDomain := Set.Ioc (0 : ℝ) 1 × Torus
def foliationCylinder : Set Vec := {x | x 0 ∈ Set.Ioc (0 : ℝ) 1}
def foliationLift (X : FoliationDomain → Vec) (x : Vec) : Vec := by
  classical
  exact if hx : x ∈ foliationCylinder then
    X (⟨x 0, hx⟩, (x 1 : PeriodicCircle), (x 2 : PeriodicCircle)) else 0

/-- A smooth embedding (0,1] × T² → Ω ∖ Γ. Each slice is an entire regular
pressure level; the outermost slice is exactly the boundary. -/
def IsPressureFoliation (Ω Γ : Set Vec) (P : Vec → ℝ) : Prop :=
  ∃ X : FoliationDomain → Vec,
    HasLocalExtensions .smooth (foliationLift X) foliationCylinder ∧
    Topology.IsEmbedding X ∧ Set.range X = Ω \ Γ ∧
    (∀ x ∈ foliationCylinder, Function.Injective (fderivWithin ℝ (foliationLift X) foliationCylinder x)) ∧
    (∀ r : Set.Ioc (0 : ℝ) 1, ∃ p : ℝ, IsRegularLevel Ω P p ∧
      Set.range (fun θ : Torus => X (r, θ)) = pressureLevel Ω P p) ∧
    Set.range (fun θ : Torus => X (⟨1, zero_lt_one, le_rfl⟩, θ)) = frontier Ω

/-! ## 4. Smooth families and non-isolation
One extension to an open parameter neighborhood includes both endpoints.
Smoothness is joint in the parameter and the spatial variables. -/
def SmoothFamily (I : Set ℝ) (c : I → Representative) : Prop :=
  ∃ U : Set ℝ, IsOpen U ∧ I ⊆ U ∧ ∃ e : ℝ → Representative,
    (∀ lambda : I, e lambda.val = c lambda) ∧
    HasLocalExtensions .smooth (fun z : ℝ × Vec => periodicLift (e z.1).position z.2) (U ×ˢ cylinder) ∧
    HasLocalExtensions .smooth (fun z : ℝ × Vec => periodicLift (e z.1).magnetic z.2) (U ×ˢ cylinder) ∧
    HasLocalExtensions .smooth (fun z : ℝ × Vec => periodicLift (e z.1).pressure z.2) (U ×ˢ cylinder)

/-- The curve of moduli classes is continuous and injective. Every interior
member is non-isolated: its singleton is not open in the full quotient. -/
def ModuliCurve (r : Regularity) (I : Set ℝ) (c : I → Representative) : Prop :=
  ∃ h : ∀ lambda, IsConfiguration r (c lambda),
    let f := fun lambda => moduliClass r ⟨c lambda, h lambda⟩
    Continuous f ∧ Function.Injective f ∧
      ∀ lambda : I, lambda.val ∈ interior I → ¬ IsOpen ({f lambda} : Set (ModuliSpace r))
end Grad.ShowcaseSurface.MainTarget

namespace Grad.ShowcaseSurface.Public
open Grad.ShowcaseSurface.MainTarget

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
  sorry

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
  sorry

end Grad.ShowcaseSurface.Public
