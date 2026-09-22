import Q24PolynomialExtension
import N3AllOrders

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped BigOperators ContDiff

namespace Grad.Q24Realization

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearQuotientBounds Grad.NonlinearProduct
open Grad.AxisCore Grad.QuotientProjection

def polynomialPart (parameters : PhaseParameters) (cellLength : ℝ) :
    (arity : ℕ) → MultilinearMap ℂ (fun _ : Fin arity => QuotientState parameters)
      (QuotientRows parameters)
  | 0 => quotientDegreeZeroPart parameters
  | 1 => quotientDegreeOnePart parameters cellLength
  | 2 => quotientDegreeTwoPart parameters cellLength
  | 3 => quotientDegreeThreePart parameters
  | 4 => quotientDegreeFourPart parameters
  | _ + 5 => 0

theorem polynomialPart_completion_exists (parameters : PhaseParameters) (cellLength : ℝ)
    (grade arity : ℕ) :
    ∃ completed : ContinuousMultilinearMap ℝ
        (fun _ : Fin arity => PolynomialState parameters (grade + 6)) (ZAmbient parameters grade),
      ∀ arguments : Fin arity → QuotientState parameters,
        completed (fun position => polynomialStateEmbed parameters (grade + 6) (arguments position)) =
          quotientEta parameters grade (polynomialPart parameters cellLength arity arguments) := by
  rcases arity with _ | arity
  · apply homogeneousCompletion_exists
    obtain ⟨constant, nonneg, bounded⟩ := quotientDegreeZeroPart_bound (parameters := parameters) grade
    exact ⟨constant, nonneg, fun arguments => by simpa [polynomialPart] using bounded arguments⟩
  rcases arity with _ | arity
  · exact homogeneousCompletion_of_oneHigh parameters grade 1 _
      (quotientDegreeOnePart_bound cellLength grade)
  rcases arity with _ | arity
  · exact homogeneousCompletion_of_oneHigh parameters grade 2 _
      (quotientDegreeTwoPart_bound cellLength grade)
  rcases arity with _ | arity
  · exact homogeneousCompletion_of_oneHigh parameters grade 3 _
      (quotientDegreeThreePart_bound grade)
  rcases arity with _ | arity
  · exact homogeneousCompletion_of_oneHigh parameters grade 4 _
      (quotientDegreeFourPart_bound grade)
  · exact ⟨0, fun _ => by simp [polynomialPart]⟩

def completedPolynomialPart (parameters : PhaseParameters) (cellLength : ℝ) (grade arity : ℕ) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin arity => PolynomialState parameters (grade + 6)) (ZAmbient parameters grade) :=
  Classical.choose (polynomialPart_completion_exists parameters cellLength grade arity)

theorem completedPolynomialPart_core (parameters : PhaseParameters) (cellLength : ℝ)
    (grade arity : ℕ) (arguments : Fin arity → QuotientState parameters) :
    completedPolynomialPart parameters cellLength grade arity
      (fun position => polynomialStateEmbed parameters (grade + 6) (arguments position)) =
      quotientEta parameters grade (polynomialPart parameters cellLength arity arguments) :=
  Classical.choose_spec (polynomialPart_completion_exists parameters cellLength grade arity) arguments

def completedPolynomial (parameters : PhaseParameters) (cellLength : ℝ) (grade : ℕ)
    (state : PolynomialState parameters (grade + 6)) : ZAmbient parameters grade :=
  ∑ arity : Fin 5, completedPolynomialPart parameters cellLength grade arity (fun _ => state)

theorem completedPolynomial_contDiff (parameters : PhaseParameters) (cellLength : ℝ) (grade : ℕ) :
    ContDiff ℝ ∞ (completedPolynomial parameters cellLength grade) := by
  apply ContDiff.sum
  intro arity _
  exact (completedPolynomialPart parameters cellLength grade arity).contDiff.comp
    (contDiff_pi.2 fun _ => contDiff_id)

theorem completedPolynomial_core (parameters : PhaseParameters) (cellLength : ℝ)
    (grade : ℕ) (state : QuotientState parameters) :
    completedPolynomial parameters cellLength grade (polynomialStateEmbed parameters (grade + 6) state) =
      quotientEta parameters grade (quotientPolynomialRows parameters cellLength state) := by
  unfold completedPolynomial
  simp only [completedPolynomialPart_core, ← map_sum]
  congr 1
  have equality := quotientRowsDerivative_zeroth cellLength state (fun position => position.elim0)
  simp only [quotientRowsDerivative, diagonalDerivative_zeroth] at equality
  simpa [Fin.sum_univ_succ, polynomialPart, add_assoc] using equality

/-- The accepted placement formula and Q4's filtered-function formula are
the same finite sum; no derivative assumption is introduced. -/
theorem placement_sum_eq_diagonal {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] {arity order : ℕ}
    (mapping : MultilinearMap ℂ (fun _ : Fin arity => E) F)
    (base : E) (directions : Fin order → E) :
    (∑ placement : Fin order ↪ Fin arity,
      mapping (Grad.CoefficientMajorants.multilinearPlacedFactor placement base directions)) =
      diagonalDerivative mapping order base directions := by
  classical
  unfold diagonalDerivative
  apply Finset.sum_bij (fun placement _ => placement.toFun)
  · intro placement _
    exact mem_slotInjections.2 placement.injective
  · intro first _ second _ equality
    exact Function.Embedding.ext (congrFun equality)
  · intro insertion member
    exact ⟨⟨insertion, mem_slotInjections.1 member⟩, Finset.mem_univ _, rfl⟩
  · intro placement _
    rfl

theorem completedPolynomialPart_derivative_core (parameters : PhaseParameters) (cellLength : ℝ)
    (grade arity order : ℕ) (base : QuotientState parameters)
    (directions : Fin order → QuotientState parameters) :
    iteratedFDeriv ℝ order
      (fun state => completedPolynomialPart parameters cellLength grade arity (fun _ => state))
      (polynomialStateEmbed parameters (grade + 6) base)
      (fun position => polynomialStateEmbed parameters (grade + 6) (directions position)) =
      quotientEta parameters grade
        (diagonalDerivative (polynomialPart parameters cellLength arity) order base directions) := by
  rw [Grad.CoefficientMajorants.ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal_all_orders]
  rw [← placement_sum_eq_diagonal, map_sum]
  apply Finset.sum_congr rfl
  intro placement _
  have placementMap :
      Grad.CoefficientMajorants.multilinearPlacedFactor placement
        (polynomialStateEmbed parameters (grade + 6) base)
        (fun position => polynomialStateEmbed parameters (grade + 6) (directions position)) =
      fun slot => polynomialStateEmbed parameters (grade + 6)
        (Grad.CoefficientMajorants.multilinearPlacedFactor placement base directions slot) := by
    funext slot
    unfold Grad.CoefficientMajorants.multilinearPlacedFactor
    split <;> rfl
  rw [placementMap, completedPolynomialPart_core]

end Grad.Q24Realization
