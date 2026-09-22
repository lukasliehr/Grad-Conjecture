import AKC6FiniteGradeInverseCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open Set
open scoped Topology ContDiff
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients

theorem FiniteGradeSmooth.congr {source target : ℕ} {parameters : PhaseParameters} {domain : Set ℝ}
    {first second : ℕ → ℝ → CellL2 source →L[ℂ] CellL2 target}
    (regular : FiniteGradeSmooth parameters domain first)
    (same : ∀ grade radius, radius ∈ domain → second grade radius = first grade radius) :
    FiniteGradeSmooth parameters domain second := by
  intro grade order
  obtain ⟨reserve, smooth⟩ := regular grade order
  exact ⟨reserve, smooth.congr (fun radius inside => congrArg
    (fun mapping : CellL2 source →L[ℂ] CellL2 target => mapping.comp (hilbertReserve parameters source reserve))
      (same grade radius inside))⟩

theorem contDiffOn_reserve {source target : ℕ} (parameters : PhaseParameters) (reserve : ℕ)
    {domain : Set ℝ} {order : WithTop ℕ∞} {action : ℝ → CellL2 source →L[ℂ] CellL2 target}
    (smooth : ContDiffOn ℝ order action domain) :
    ContDiffOn ℝ order (fun radius => (action radius).comp (hilbertReserve parameters source reserve)) domain :=
  (reserveOperator (source := source) (target := target) parameters reserve).contDiff.comp_contDiffOn smooth

theorem FiniteGradeSmooth.add {source target : ℕ} {parameters : PhaseParameters} {domain : Set ℝ}
    {first second : ℕ → ℝ → CellL2 source →L[ℂ] CellL2 target}
    (one : FiniteGradeSmooth parameters domain first) (two : FiniteGradeSmooth parameters domain second) :
    FiniteGradeSmooth parameters domain (fun grade radius => first grade radius + second grade radius) := by
  intro grade order
  obtain ⟨a, ha⟩ := one grade order
  obtain ⟨b, hb⟩ := two grade order
  refine ⟨a + b, ((contDiffOn_reserve parameters b ha).add (contDiffOn_reserve parameters a hb)).congr ?_⟩
  intro radius _
  rw [ContinuousLinearMap.add_comp]
  apply congrArg₂ (· + ·)
  · rw [hilbertReserve_add, ContinuousLinearMap.comp_assoc]
  · rw [Nat.add_comm a b, hilbertReserve_add, ContinuousLinearMap.comp_assoc]

theorem FiniteGradeSmooth.neg {source target : ℕ} {parameters : PhaseParameters} {domain : Set ℝ}
    {action : ℕ → ℝ → CellL2 source →L[ℂ] CellL2 target}
    (regular : FiniteGradeSmooth parameters domain action) :
    FiniteGradeSmooth parameters domain (fun grade radius => -(action grade radius)) := by
  intro grade order
  obtain ⟨reserve, smooth⟩ := regular grade order
  exact ⟨reserve, smooth.neg.congr (fun radius _ => ContinuousLinearMap.neg_comp _ _)⟩

theorem FiniteGradeSmooth.smul {source target : ℕ} {parameters : PhaseParameters} {domain : Set ℝ}
    {action : ℕ → ℝ → CellL2 source →L[ℂ] CellL2 target} {scalar : ℝ → ℂ}
    (regular : FiniteGradeSmooth parameters domain action) (scalarSmooth : ContDiffOn ℝ ∞ scalar domain) :
    FiniteGradeSmooth parameters domain (fun grade radius => scalar radius • action grade radius) := by
  intro grade order
  obtain ⟨reserve, smooth⟩ := regular grade order
  refine ⟨reserve, ((scalarSmooth.of_le (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).smul smooth).congr ?_⟩
  intro radius _
  exact ContinuousLinearMap.smul_comp _ _ _

end Grad.AnnularWeightedSmoothness
