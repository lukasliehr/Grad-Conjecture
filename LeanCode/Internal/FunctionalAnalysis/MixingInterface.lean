import WeakH1

noncomputable section

namespace Grad.HilbertMixing

variable {Index : Type*} [Fintype Index] [DecidableEq Index]
variable {Value : Type*} [NormedAddCommGroup Value] [InnerProductSpace ℝ Value]

def mix (coefficients : Index → Index → ℝ) (field : PiLp 2 (fun _ : Index => Value)) :
    PiLp 2 (fun _ : Index => Value) :=
  WithLp.toLp 2 (fun output => ∑ input, coefficients input output • field input)

def normSqGoal : Prop :=
  ∀ (coefficients : Index → Index → ℝ),
    (∀ first second, ∑ output, coefficients first output * coefficients second output =
      if first = second then 1 else 0) →
    ∀ field : PiLp 2 (fun _ : Index => Value), ‖mix coefficients field‖ ^ 2 = ‖field‖ ^ 2

def fieldNormSqGoal (rank : ℕ) : Prop :=
  normSqGoal (Index := Fin rank → Fin 2) (Value := Grad.PDEBootstrap.FieldL2)

#check @mix
#check @normSqGoal
#check fieldNormSqGoal
#check PiLp.norm_sq_eq_of_L2
#check real_inner_self_eq_norm_sq
#check sum_inner
#check inner_sum
#check real_inner_smul_left
#check real_inner_smul_right
#check Finset.sum_comm
#check Finset.sum_mul
#check Finset.mul_sum

end Grad.HilbertMixing
