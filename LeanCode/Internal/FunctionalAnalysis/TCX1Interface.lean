import TL1TensorLpInterface

noncomputable section

universe indexUniverse valueUniverse

namespace Grad.TensorCellExchange

variable (Index : Type indexUniverse) [Fintype Index]
variable (Value : Type valueUniverse) [NormedAddCommGroup Value] [NormedSpace ℂ Value]

def collectCoordinates (tensor : PiLp 2 (fun _ : Index => lp (fun _ : ℤ => Value) 2)) :
    ℤ → PiLp 2 (fun _ : Index => Value) :=
  fun cell => WithLp.toLp 2 (fun index => tensor index cell)

def separateCoordinates (cells : lp (fun _ : ℤ => PiLp 2 (fun _ : Index => Value)) 2) :
    Index → ℤ → Value :=
  fun index cell => cells cell index

def SquareSumGoal : Prop :=
  (∀ tensor : PiLp 2 (fun _ : Index => lp (fun _ : ℤ => Value) 2),
    ‖tensor‖ ^ 2 = ∑ index : Index, ∑' cell : ℤ, ‖tensor index cell‖ ^ 2) ∧
  (∀ cells : lp (fun _ : ℤ => PiLp 2 (fun _ : Index => Value)) 2,
    ‖cells‖ ^ 2 = ∑ index : Index, ∑' cell : ℤ, ‖cells cell index‖ ^ 2)

def ExchangeGoal : Prop :=
  ∃ exchange :
      PiLp 2 (fun _ : Index => lp (fun _ : ℤ => Value) 2) ≃ₗᵢ[ℂ]
        lp (fun _ : ℤ => PiLp 2 (fun _ : Index => Value)) 2,
    (∀ tensor cell index, exchange tensor cell index = tensor index cell) ∧
    (∀ cells index cell, exchange.symm cells index cell = cells cell index) ∧
    (∀ tensor, ‖exchange tensor‖ = ‖tensor‖)

def BlockGoal : Prop := SquareSumGoal Index Value ∧ ExchangeGoal Index Value

def OrderedConsumerGoal : Prop :=
  ∀ rank : ℕ,
    (∀ tensor : Grad.TensorLpExchange.OrderedCellValues rank,
      ‖tensor‖ ^ 2 = ∑ word : Fin rank → Fin 2, ∑' cell : ℤ, ‖tensor word cell‖ ^ 2) ∧
    (∀ cells : lp (fun _ : ℤ => PiLp 2 (fun _ : Fin rank → Fin 2 =>
        EuclideanSpace ℂ (Fin 3))) 2,
      ‖cells‖ ^ 2 = ∑ word : Fin rank → Fin 2, ∑' cell : ℤ, ‖cells cell word‖ ^ 2) ∧
    ∃ exchange : Grad.TensorLpExchange.OrderedCellValues rank ≃ₗᵢ[ℂ]
        lp (fun _ : ℤ => PiLp 2 (fun _ : Fin rank → Fin 2 => EuclideanSpace ℂ (Fin 3))) 2,
      (∀ tensor cell word, exchange tensor cell word = tensor word cell) ∧
      (∀ cells word cell, exchange.symm cells word cell = cells cell word) ∧
      (∀ tensor, ‖exchange tensor‖ = ‖tensor‖)

end Grad.TensorCellExchange
