import AKDN18ActualBalancedFluxEulerNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalCartesianTameEstimate

/-- Finite ordered sums retain coefficient weights until the single joint
allocation is applied. No product of coarse high-order estimates occurs. -/
theorem weightedEulerList_bound {Index : Type*} (terms : List Index) (weight value : Index → ℝ)
    (external payment : ℝ)
    (bound : ∀ term ∈ terms, external*value term ≤ weight term*payment) :
    external*(terms.map value).sum ≤ (terms.map weight).sum*payment := by
  induction terms with
  | nil => simp only [List.map_nil,List.sum_nil,mul_zero,zero_mul,le_refl]
  | cons term terms previous =>
      simp only [List.map_cons,List.sum_cons,mul_add,add_mul]
      exact add_le_add (bound term List.mem_cons_self)
        (previous (fun item member => bound item (List.mem_cons_of_mem term member)))

/-- SR19–20's weighted Euler induction. A term records coefficient rank,
terminal frequency grade and strictly lower Euler rank. Product budgets
are combined before induction, so total rank is charged exactly once. -/
theorem jointWeightedEulerInduction (total : ℕ) (budget : ℕ → ℝ) (unknown forcing : ℕ → ℕ → ℝ)
    (terms : ℕ → ℕ → List (ℕ × ℕ × ℕ)) (weight : ℕ → ℕ → (ℕ × ℕ × ℕ) → ℝ)
    (pairConstant weightConstant terminal : ℝ)
    (pair0 : 0 ≤ pairConstant) (weight0 : 0 ≤ weightConstant) (terminal0 : 0 ≤ terminal)
    (budget0 : ∀ order, 0 ≤ budget order) (unknown0 : ∀ order grade, 0 ≤ unknown order grade)
    (pair : ∀ first second, first+second ≤ total →
      budget first*budget second ≤ pairConstant*budget (first+second))
    (pure : ∀ extra grade, extra+grade ≤ total → budget extra*unknown 0 grade ≤ terminal)
    (source : ∀ extra order grade, extra+order+grade+1 ≤ total → budget extra*forcing order grade ≤ terminal)
    (allocated : ∀ order grade term, term ∈ terms order grade →
      term.2.2 ≤ order ∧ term.1+term.2.1+term.2.2 ≤ order+grade+1)
    (weights : ∀ order grade term, term ∈ terms order grade → 0 ≤ weight order grade term)
    (weightSum : ∀ order grade, order+grade+1 ≤ total →
      ((terms order grade).map (weight order grade)).sum ≤ weightConstant)
    (recurrence : ∀ order grade, order+grade+1 ≤ total →
      unknown (order+1) grade ≤ forcing order grade+
        ((terms order grade).map (fun term => weight order grade term*budget term.1*unknown term.2.2 term.2.1)).sum) :
    ∀ order extra grade, extra+grade+order ≤ total →
      budget extra*unknown order grade ≤ (1+pairConstant*weightConstant)^order*terminal := by
  let gain := 1+pairConstant*weightConstant
  have gainOne : 1 ≤ gain := by dsimp only [gain]; linarith [mul_nonneg pair0 weight0]
  have gain0 : 0 ≤ gain := zero_le_one.trans gainOne
  intro order
  induction order using Nat.strong_induction_on with
  | h order previous =>
      intro extra grade paid
      cases order with
      | zero => simpa only [pow_zero,one_mul,Nat.add_zero] using pure extra grade paid
      | succ order =>
          have recurrenceBound := mul_le_mul_of_nonneg_left (recurrence order grade (by omega)) (budget0 extra)
          rw [mul_add] at recurrenceBound
          have pointBound (term : ℕ × ℕ × ℕ) (member : term ∈ terms order grade) :
              budget extra*(weight order grade term*budget term.1*unknown term.2.2 term.2.1) ≤
                weight order grade term*(pairConstant*gain^order*terminal) := by
            have ranks := allocated order grade term member
            have joint := pair extra term.1 (by omega)
            have lower := previous term.2.2 (by omega) (extra+term.1) term.2.1 (by omega)
            have power : gain^term.2.2 ≤ gain^order := pow_le_pow_right₀ gainOne ranks.1
            have lowerBound : budget (extra+term.1)*unknown term.2.2 term.2.1 ≤ gain^order*terminal :=
              lower.trans (mul_le_mul_of_nonneg_right power terminal0)
            have combined := mul_le_mul_of_nonneg_left
              ((mul_le_mul_of_nonneg_right joint (unknown0 _ _)).trans
                (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left lowerBound pair0))
              (weights order grade term member)
            calc
              _ = weight order grade term*((budget extra*budget term.1)*unknown term.2.2 term.2.1) := by ring
              _ ≤ weight order grade term*(pairConstant*(gain^order*terminal)) := combined
              _ = _ := by ring
          have sumBound := weightedEulerList_bound (terms order grade) (weight order grade)
            (fun term => weight order grade term*budget term.1*unknown term.2.2 term.2.1)
            (budget extra) (pairConstant*gain^order*terminal) pointBound
          have sumPaid := sumBound.trans (mul_le_mul_of_nonneg_right (weightSum order grade (by omega))
            (mul_nonneg (mul_nonneg pair0 (pow_nonneg gain0 order)) terminal0))
          have terminalLe : terminal ≤ gain^order*terminal := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ gainOne) terminal0
          have result := recurrenceBound.trans (add_le_add (source extra order grade (by omega)) sumPaid)
          change budget extra*unknown (order+1) grade ≤ gain^(order+1)*terminal
          apply result.trans
          rw [pow_succ]
          dsimp only [gain] at terminalLe ⊢
          nlinarith only [terminalLe]

end Grad.OriginalCartesianTameEstimate
