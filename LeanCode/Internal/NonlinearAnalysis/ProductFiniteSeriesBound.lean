import ProductSequenceConvolution

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearProduct

theorem norm_hasSum_le_finite_majorants {Index Choice Value : Type} [Fintype Choice]
    [NormedAddCommGroup Value] [CompleteSpace Value]
    (kernel : Index → Value) (value : Value) (kernelSum : HasSum kernel value)
    (majorants : Choice → Index → ℝ) (totals coefficients : Choice → ℝ)
    (majorantSums : ∀ choice, HasSum (majorants choice) (totals choice))
    (dominated : ∀ index, ‖kernel index‖ ≤ ∑ choice, coefficients choice * majorants choice index) :
    ‖value‖ ≤ ∑ choice, coefficients choice * totals choice := by
  have majorantSum : HasSum (fun index => ∑ choice, coefficients choice * majorants choice index)
      (∑ choice, coefficients choice * totals choice) :=
    hasSum_sum (fun choice _ => (majorantSums choice).mul_left (coefficients choice))
  have normSummable : Summable (fun index => ‖kernel index‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) dominated majorantSum.summable
  calc
    _ = ‖∑' index, kernel index‖ := congrArg norm kernelSum.tsum_eq.symm
    _ ≤ ∑' index, ‖kernel index‖ := norm_tsum_le_tsum_norm normSummable
    _ ≤ ∑' index, ∑ choice, coefficients choice * majorants choice index :=
      normSummable.tsum_le_tsum dominated majorantSum.summable
    _ = _ := majorantSum.tsum_eq

end Grad.NonlinearProduct
