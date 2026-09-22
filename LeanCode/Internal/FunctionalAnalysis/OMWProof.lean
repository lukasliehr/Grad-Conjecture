import OMWInterface
import WTCProof

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Grad.OrderedMultiplicity.Weak

open Grad.GenericCarriers
open Grad.PDEBootstrap (Spatial)

theorem derivative_eq_canonical (dimension rank : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (field : FieldL2 dimension domain)
    (derivatives : OrderedFields dimension rank domain)
    (weakFamily : IsWeakDerivativeFamily dimension rank domain field derivatives)
    (word : Fin rank → Fin 2) : derivatives word =
      canonicalFamily dimension rank domain derivatives (countZeros word) :=
  Grad.WeakTesting.Commutation.weakEquality dimension domain openDomain rank word
    (canonicalWord rank (countZeros word)) (sameCounts_canonical rank word)
    field (derivatives word) (derivatives (canonicalWord rank (countZeros word)))
    (weakFamily word) (weakFamily (canonicalWord rank (countZeros word)))

theorem derivatives_eq_orderedTensor (dimension rank : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (field : FieldL2 dimension domain)
    (derivatives : OrderedFields dimension rank domain)
    (weakFamily : IsWeakDerivativeFamily dimension rank domain field derivatives) :
    derivatives = orderedTensor rank (canonicalFamily dimension rank domain derivatives) := by
  apply PiLp.ext
  intro word
  exact derivative_eq_canonical dimension rank domain openDomain field derivatives weakFamily word

theorem identification : IdentificationGoal := fun dimension rank domain openDomain field derivatives weakFamily =>
  ⟨derivative_eq_canonical dimension rank domain openDomain field derivatives weakFamily,
    derivatives_eq_orderedTensor dimension rank domain openDomain field derivatives weakFamily⟩

theorem weak_multiplicity_formula (dimension rank : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (field : FieldL2 dimension domain)
    (derivatives : OrderedFields dimension rank domain)
    (weakFamily : IsWeakDerivativeFamily dimension rank domain field derivatives) :
    ∑ word : Fin rank → Fin 2, ‖derivatives word‖ ^ 2 =
      ∑ zeros : Fin (rank + 1), (rank.choose zeros.val : ℝ) *
        ‖canonicalFamily dimension rank domain derivatives zeros‖ ^ 2 := by
  calc
    _ = ∑ word : Fin rank → Fin 2,
        ‖canonicalFamily dimension rank domain derivatives (countZeros word)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro word _
      rw [derivative_eq_canonical dimension rank domain openDomain field derivatives weakFamily word]
    _ = _ := multiplicity_formula rank (canonicalFamily dimension rank domain derivatives)

theorem multiplicity : MultiplicityGoal := by
  intro dimension rank domain openDomain field derivatives weakFamily
  have sumEquality := weak_multiplicity_formula dimension rank domain openDomain field derivatives weakFamily
  exact ⟨sumEquality, (tensor_norm_sq rank derivatives).trans sumEquality⟩

theorem multiIndex : MultiIndexGoal := by
  intro dimension rank domain openDomain field derivatives weakFamily
  refine (weak_multiplicity_formula dimension rank domain openDomain field derivatives weakFamily).trans ?_
  apply Fintype.sum_equiv (multiIndexEquiv rank) _ _
  intro zeros
  change (rank.choose zeros.val : ℝ) * ‖canonicalFamily dimension rank domain derivatives zeros‖ ^ 2 =
    (rank.choose zeros.val : ℝ) * ‖canonicalFamily dimension rank domain derivatives
      ((multiIndexEquiv rank).symm (multiIndexEquiv rank zeros))‖ ^ 2
  rw [Equiv.symm_apply_apply]

theorem normComparison : NormGoal := by
  intro dimension rank domain openDomain field derivatives weakFamily
  have comparison := norm_comparison rank (canonicalFamily dimension rank domain derivatives)
  have normEquality : topOrdered rank (canonicalFamily dimension rank domain derivatives) = ‖derivatives‖ :=
    (congrArg norm (derivatives_eq_orderedTensor dimension rank domain openDomain field derivatives weakFamily)).symm
  rw [normEquality] at comparison
  exact comparison

theorem derivative_zero (dimension : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (field : FieldL2 dimension domain) (derivatives : OrderedFields dimension 0 domain)
    (weakFamily : IsWeakDerivativeFamily dimension 0 domain field derivatives)
    (word : Fin 0 → Fin 2) : derivatives word = field :=
  (Grad.WeakTesting.Commutation.zero dimension domain openDomain word field (derivatives word)).mp
    (weakFamily word)

theorem zero : ZeroGoal := by
  intro dimension domain openDomain field derivatives weakFamily
  have allEqual := derivative_zero dimension domain openDomain field derivatives weakFamily
  have canonicalEqual : canonicalFamily dimension 0 domain derivatives 0 = field :=
    allEqual (canonicalWord 0 0)
  refine ⟨allEqual, ?_, ?_⟩
  · calc
      ‖derivatives‖ = topOrdered 0 (canonicalFamily dimension 0 domain derivatives) :=
        congrArg norm (derivatives_eq_orderedTensor dimension 0 domain openDomain field derivatives weakFamily)
      _ = ‖canonicalFamily dimension 0 domain derivatives 0‖ := topOrdered_zero _
      _ = ‖field‖ := congrArg norm canonicalEqual
  · change topMulti 0 (canonicalFamily dimension 0 domain derivatives) = ‖field‖
    rw [topMulti_zero, canonicalEqual]

theorem block : BlockGoal := ⟨identification, multiplicity, multiIndex, normComparison, zero⟩

end Grad.OrderedMultiplicity.Weak
