import AKDK4FiniteEulerEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set
namespace Grad.OriginalRadialRecovery
open Grad.OriginalCartesianTameEstimate Grad.OriginalTerminalAllocation

/-- The finite polynomial P_r(E)=E(E-1)...(E-r+1). -/
def inverseEulerStep (rank : ℕ) : List (ℕ × ℝ) → List (ℕ × ℝ) :=
  List.rec [] (fun term _ previous => (term.1+1,term.2)::(term.1,-(rank:ℝ)*term.2)::previous)

def inverseEulerTerms : ℕ → List (ℕ × ℝ) :=
  Nat.rec [(0,1)] (fun rank previous => inverseEulerStep rank previous)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def eulerCombination (jets : ℕ → ℝ → E) (terms : List (ℕ × ℝ)) (radius : ℝ) : E :=
  List.rec 0 (fun term _ previous => term.2 • jets term.1 radius + previous) terms

theorem eulerCombination_step (jets : ℕ → ℝ → E) (terms : List (ℕ × ℝ))
    (rank : ℕ) (radius : ℝ) :
    eulerCombination jets (inverseEulerStep rank terms) radius =
      eulerCombination (fun order => jets (order+1)) terms radius -
        (rank:ℝ) • eulerCombination jets terms radius := by
  induction terms with
  | nil => simp [inverseEulerStep,eulerCombination]
  | cons term terms previous =>
      simp only [inverseEulerStep,eulerCombination] at previous ⊢
      rw [previous]
      module

theorem inverseEulerStep_rank (rank : ℕ) (terms : List (ℕ × ℝ))
    (bound : ∀ term ∈ terms,term.1≤rank) :
    ∀ term ∈ inverseEulerStep rank terms,term.1≤rank+1 := by
  induction terms with
  | nil => simp [inverseEulerStep]
  | cons head terms previous =>
      intro term member
      change term ∈ (head.1+1,head.2)::(head.1,-(rank:ℝ)*head.2)::inverseEulerStep rank terms at member
      simp only [List.mem_cons] at member
      rcases member with same | same | tail
      · subst term; have := bound head List.mem_cons_self; dsimp; omega
      · subst term; have := bound head List.mem_cons_self; dsimp; omega
      · exact previous (fun term member => bound term (List.mem_cons_of_mem head member)) term tail

theorem inverseEulerTerms_rank (rank : ℕ) :
    ∀ term ∈ inverseEulerTerms rank,term.1≤rank := by
  induction rank with
  | zero =>
      intro term member
      have same : term=(0,1) := List.mem_singleton.mp member
      subst term
      exact le_rfl
  | succ rank previous => exact inverseEulerStep_rank rank (inverseEulerTerms rank) previous

theorem eulerCombination_continuousOn (domain : Set ℝ) (jets : ℕ → ℝ → E)
    (continuous : ∀ rank,ContinuousOn (jets rank) domain) (terms : List (ℕ × ℝ)) :
    ContinuousOn (eulerCombination jets terms) domain := by
  induction terms with
  | nil => exact continuousOn_const
  | cons term terms previous => exact ((continuous term.1).const_smul term.2).add previous

theorem eulerCombination_hasDerivWithinAt (domain : Set ℝ) (jets : ℕ → ℝ → E)
    (radius : ℝ) (derivative : ∀ rank,
      HasDerivWithinAt (jets rank) (radius⁻¹ • jets (rank+1) radius) domain radius)
    (terms : List (ℕ × ℝ)) :
    HasDerivWithinAt (eulerCombination jets terms)
      (radius⁻¹ • eulerCombination (fun rank => jets (rank+1)) terms radius) domain radius := by
  induction terms with
  | nil =>
      change HasDerivWithinAt (fun _ : ℝ => (0:E)) (radius⁻¹ • (0:E)) domain radius
      simpa only [smul_zero] using hasDerivWithinAt_const radius domain (0:E)
  | cons term terms previous =>
      have result := ((derivative term.1).const_smul term.2).add previous
      apply result.congr_deriv
      simp only [eulerCombination]
      module

end Grad.OriginalRadialRecovery
