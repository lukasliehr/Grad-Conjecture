import QuotientPolynomialTerms

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

variable {parameters : PhaseParameters}

/-- Genuine directional differentiability of every order of the literal O14
derivative family: the `order`-th derivative map, with its first `order`
directions frozen, has the `order+1`-st derivative as directional derivative
along the final direction, in every original grade norm. -/
theorem quotientRowsDerivative_genuine (cellLength : ℝ) (order : ℕ)
    (base : QuotientState parameters)
    (directions : Fin (order + 1) → QuotientState parameters) :
    IsRowsDirectionalDerivative
      (fun state => quotientRowsDerivative parameters cellLength order state
        (fun position => directions position.castSucc))
      base (directions (Fin.last order))
      (quotientRowsDerivative parameters cellLength (order + 1) base directions) := by
  obtain ⟨zeroCoefficients, _, zeroOne, zeroVanish, zeroExpansion⟩ :=
    diagonalDerivative_expansion (quotientDegreeZeroPart parameters) order base
      (directions (Fin.last order)) (fun position => directions position.castSucc)
  obtain ⟨oneCoefficients, _, oneOne, oneVanish, oneExpansion⟩ :=
    diagonalDerivative_expansion (quotientDegreeOnePart parameters cellLength) order base
      (directions (Fin.last order)) (fun position => directions position.castSucc)
  obtain ⟨twoCoefficients, _, twoOne, twoVanish, twoExpansion⟩ :=
    diagonalDerivative_expansion (quotientDegreeTwoPart parameters cellLength) order base
      (directions (Fin.last order)) (fun position => directions position.castSucc)
  obtain ⟨threeCoefficients, _, threeOne, threeVanish, threeExpansion⟩ :=
    diagonalDerivative_expansion (quotientDegreeThreePart parameters) order base
      (directions (Fin.last order)) (fun position => directions position.castSucc)
  obtain ⟨fourCoefficients, _, fourOne, fourVanish, fourExpansion⟩ :=
    diagonalDerivative_expansion (quotientDegreeFourPart parameters) order base
      (directions (Fin.last order)) (fun position => directions position.castSucc)
  have snocDirections : Fin.snoc (fun position => directions position.castSucc)
      (directions (Fin.last order)) = directions := Fin.snoc_init_self directions
  have combinedOne : zeroCoefficients 1 + oneCoefficients 1 + twoCoefficients 1 +
      threeCoefficients 1 + fourCoefficients 1 =
      quotientRowsDerivative parameters cellLength (order + 1) base directions := by
    rw [zeroOne, oneOne, twoOne, threeOne, fourOne, snocDirections]
    rfl
  have expansion : ∀ t : ℝ,
      (fun state => quotientRowsDerivative parameters cellLength order state
        (fun position => directions position.castSucc))
        (base + (t : ℂ) • directions (Fin.last order)) =
      ∑ power ∈ Finset.range 6, ((t : ℂ) ^ power) •
        (zeroCoefficients power + oneCoefficients power + twoCoefficients power +
          threeCoefficients power + fourCoefficients power) := by
    intro t
    have padded {slots : ℕ} (slotBound : slots + 1 ≤ 6)
        (coefficients : ℕ → QuotientRows parameters)
        (vanish : ∀ power, slots < power → coefficients power = 0) :
        (∑ power ∈ Finset.range (slots + 1), ((t : ℂ) ^ power) • coefficients power) =
          ∑ power ∈ Finset.range 6, ((t : ℂ) ^ power) • coefficients power := by
      apply Finset.sum_subset
      · intro member membership
        rw [Finset.mem_range] at membership ⊢
        omega
      · intro power _ outside
        rw [Finset.mem_range, not_lt] at outside
        rw [vanish power (by omega), smul_zero]
    show quotientRowsDerivative parameters cellLength order
        (base + (t : ℂ) • directions (Fin.last order))
        (fun position => directions position.castSucc) = _
    unfold quotientRowsDerivative
    rw [zeroExpansion t, oneExpansion t, twoExpansion t, threeExpansion t, fourExpansion t,
      padded (by omega) zeroCoefficients zeroVanish,
      padded (by omega) oneCoefficients oneVanish,
      padded (by omega) twoCoefficients twoVanish,
      padded (by omega) threeCoefficients threeVanish,
      padded (by omega) fourCoefficients fourVanish,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro power _
    rw [smul_add, smul_add, smul_add, smul_add]
  have conclusion := polynomial_rows_directional 4
    (fun power => zeroCoefficients power + oneCoefficients power + twoCoefficients power +
      threeCoefficients power + fourCoefficients power)
    (fun state => quotientRowsDerivative parameters cellLength order state
      (fun position => directions position.castSucc))
    base (directions (Fin.last order)) expansion
  rw [combinedOne] at conclusion
  exact conclusion

end Grad.NonlinearQuotientBounds
