import AKDN28UniformActualNativeRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.OriginalCartesianTameEstimate

theorem eulerAllocationSum_add (first second : ℕ → ℕ → ℝ) (terms : List (ℕ × ℕ)) :
    eulerAllocationSum (fun a b => first a b+second a b) terms =
      eulerAllocationSum first terms+eulerAllocationSum second terms := by
  induction terms with
  | nil => change (0:ℝ)=0+0; ring
  | cons term terms previous =>
      change (first term.1 term.2+second term.1 term.2)+eulerAllocationSum (fun a b => first a b+second a b) terms =
        (first term.1 term.2+eulerAllocationSum first terms)+(second term.1 term.2+eulerAllocationSum second terms)
      rw [previous]
      ring

/-- The exact native collector, now written in the same nested form as
the three actual physical-row estimates. No derivative allocation is lost. -/
theorem nativeEulerAllocations_weighted (budget : ℕ → ℝ) (unknown : ℕ → ℕ → ℝ) (rank grade : ℕ) :
    ((nativeEulerAllocations rank grade).map (fun term => budget term.1*unknown term.2.2 term.2.1)).sum =
      budget 0*eulerAllocationSum (fun _ terminal => unknown terminal (grade+1)) (eulerLeibnizTerms rank)+
      eulerAllocationSum (fun _ rowRank =>
        eulerAllocationSum (fun coefficient inputRank =>
          budget coefficient*eulerAllocationSum (fun _ terminal => unknown terminal (grade+1)) (eulerLeibnizTerms inputRank)+
          budget (coefficient+grade+1)*eulerAllocationSum (fun _ terminal => unknown terminal 0) (eulerLeibnizTerms inputRank))
          (eulerLeibnizTerms rowRank)) (eulerLeibnizTerms rank) := by
  rw [nativeEulerAllocations_sum rank grade (fun coefficient power order => budget coefficient*unknown order power)]
  simp only [eulerAllocationSum_mul_left,←eulerAllocationSum_add]

theorem listMappedSum_nonnegative {Index : Type*} (terms : List Index) (values : Index → ℝ)
    (nonnegative : ∀ index ∈ terms, 0 ≤ values index) : 0 ≤ (terms.map values).sum := by
  induction terms with
  | nil => exact le_rfl
  | cons term terms previous =>
      exact add_nonneg (nonnegative term List.mem_cons_self)
        (previous (fun index member => nonnegative index (List.mem_cons_of_mem term member)))

theorem nativeEulerAllocations_nonnegative (budget : ℕ → ℝ) (unknown : ℕ → ℕ → ℝ)
    (budget0 : ∀ rank, 0 ≤ budget rank) (unknown0 : ∀ rank grade, 0 ≤ unknown rank grade)
    (rank grade : ℕ) :
    0 ≤ ((nativeEulerAllocations rank grade).map (fun term => budget term.1*unknown term.2.2 term.2.1)).sum :=
  listMappedSum_nonnegative _ _ (fun _term _ => mul_nonneg (budget0 _) (unknown0 _ _))

/-- Combining the phase and literal three-row flux estimates retains the
same weighted list that enters the strictly lower Euler induction. -/
theorem nativeEulerCollector_bound (budget : ℕ → ℝ) (unknown : ℕ → ℕ → ℝ)
    (budget0 : ∀ rank, 0 ≤ budget rank) (budgetOne : 1 ≤ budget 0)
    (unknown0 : ∀ rank grade, 0 ≤ unknown rank grade) (rank grade : ℕ)
    (phase flux phaseConstant fluxConstant : ℝ) (phase0 : 0 ≤ phaseConstant) (flux0 : 0 ≤ fluxConstant)
    (phaseBound : phase ≤ phaseConstant*eulerAllocationSum
      (fun _ terminal => unknown terminal (grade+1)) (eulerLeibnizTerms rank))
    (fluxBound : flux ≤ fluxConstant*eulerAllocationSum (fun _ rowRank =>
      eulerAllocationSum (fun coefficient inputRank =>
        budget coefficient*eulerAllocationSum (fun _ terminal => unknown terminal (grade+1)) (eulerLeibnizTerms inputRank)+
        budget (coefficient+grade+1)*eulerAllocationSum (fun _ terminal => unknown terminal 0) (eulerLeibnizTerms inputRank))
        (eulerLeibnizTerms rowRank)) (eulerLeibnizTerms rank)) :
    phase+flux ≤ (phaseConstant+fluxConstant)*
      ((nativeEulerAllocations rank grade).map (fun term => budget term.1*unknown term.2.2 term.2.1)).sum := by
  rw [nativeEulerAllocations_weighted]
  have input0 (power order : ℕ) :
      0 ≤ eulerAllocationSum (fun _ terminal => unknown terminal power) (eulerLeibnizTerms order) :=
    eulerAllocationSum_nonnegative _ (fun _ _ => unknown0 _ _) _
  have fluxSum0 : 0 ≤ eulerAllocationSum (fun _ rowRank =>
      eulerAllocationSum (fun coefficient inputRank =>
        budget coefficient*eulerAllocationSum (fun _ terminal => unknown terminal (grade+1)) (eulerLeibnizTerms inputRank)+
        budget (coefficient+grade+1)*eulerAllocationSum (fun _ terminal => unknown terminal 0) (eulerLeibnizTerms inputRank))
        (eulerLeibnizTerms rowRank)) (eulerLeibnizTerms rank) :=
    eulerAllocationSum_nonnegative _ (fun _ _ => eulerAllocationSum_nonnegative _
      (fun _ _ => add_nonneg (mul_nonneg (budget0 _) (input0 _ _)) (mul_nonneg (budget0 _) (input0 _ _))) _) _
  have phasePaid : phaseConstant*eulerAllocationSum (fun _ terminal => unknown terminal (grade+1)) (eulerLeibnizTerms rank) ≤
      phaseConstant*(budget 0*eulerAllocationSum (fun _ terminal => unknown terminal (grade+1)) (eulerLeibnizTerms rank)) := by
    apply mul_le_mul_of_nonneg_left _ phase0
    simpa only [one_mul] using mul_le_mul_of_nonneg_right budgetOne (input0 (grade+1) rank)
  have weightedPhase0 := mul_nonneg (budget0 0) (input0 (grade+1) rank)
  have extraOne := mul_nonneg phase0 fluxSum0
  have extraTwo := mul_nonneg flux0 weightedPhase0
  nlinarith only [phaseBound,fluxBound,phasePaid,extraOne,extraTwo]

end Grad.OriginalCartesianTameEstimate
