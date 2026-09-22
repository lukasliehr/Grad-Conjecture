import GC1Proof

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Grad.TensorLpExchange.Generic

universe indexUniverse valueUniverse pointUniverse

variable (Index : Type indexUniverse) [Fintype Index]
variable (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
variable {Point : Type pointUniverse} [MeasurableSpace Point] (measure : Measure Point)

abbrev Values := PiLp 2 (fun _ : Index => Value)

abbrev Fields := PiLp 2 (fun _ : Index => Lp Value 2 measure)

abbrev ValueField := Lp (Values Index Value) 2 measure

def assemble (representatives : Index → Point → Value) : Point → Values Index Value :=
  fun point => WithLp.toLp 2 (fun index => representatives index point)

def separate (field : ValueField Index Value measure) : Fields Index Value measure :=
  WithLp.toLp 2 (fun index =>
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Index => Value) index).compLpL 2 measure field)

def AssemblyGoal : Prop :=
  ∀ representatives : Index → Point → Value,
    (∀ index, MemLp (representatives index) 2 measure) →
      MemLp (assemble Index Value representatives) 2 measure

def IndependenceGoal : Prop :=
  ∀ first second : Index → Point → Value,
    (∀ index, first index =ᵐ[measure] second index) →
      assemble Index Value first =ᵐ[measure] assemble Index Value second

def SquareSumGoal : Prop :=
  (∀ field : Fields Index Value measure,
    ‖field‖ ^ 2 = ∑ index : Index, ∫ point, ‖field index point‖ ^ 2 ∂measure) ∧
  (∀ field : ValueField Index Value measure,
    ‖field‖ ^ 2 = ∑ index : Index, ∫ point, ‖field point index‖ ^ 2 ∂measure)

def ExchangeGoal : Prop :=
  ∃ exchange : Fields Index Value measure ≃ₗᵢ[ℂ] ValueField Index Value measure,
    (∀ field, ∀ᵐ point ∂measure, ∀ index, exchange field point index = field index point) ∧
    (∀ field, ∀ᵐ point ∂measure, ∀ index,
      exchange.symm field index point = field point index) ∧
    (∀ field, exchange.symm field = separate Index Value measure field)

def BlockGoal : Prop :=
  AssemblyGoal Index Value measure ∧ IndependenceGoal Index Value measure ∧
    SquareSumGoal Index Value measure ∧ ExchangeGoal Index Value measure

open Grad.PDEBootstrap (Spatial)

def CanonicalGoal : Prop :=
  ∀ (dimension rank : ℕ) (domain : Set Spatial),
    ∃ exchange : Grad.GenericCarriers.OrderedFields dimension rank domain ≃ₗᵢ[ℂ]
        Grad.GenericCarriers.OrderedValueField dimension rank domain,
      (∀ field, ∀ᵐ point ∂volume.restrict domain, ∀ word : Fin rank → Fin 2,
        exchange field point word = field word point) ∧
      (∀ field, ∀ᵐ point ∂volume.restrict domain, ∀ word : Fin rank → Fin 2,
        exchange.symm field word point = field point word) ∧
      (∀ field : Grad.GenericCarriers.OrderedFields dimension rank domain,
        ‖field‖ ^ 2 = ∑ word : Fin rank → Fin 2,
        ∫ point : Spatial, ‖field word point‖ ^ 2 ∂volume.restrict domain) ∧
      (∀ field, ‖exchange field‖ ^ 2 = ∑ word : Fin rank → Fin 2,
        ∫ point : Spatial, ‖field word point‖ ^ 2 ∂volume.restrict domain)

end Grad.TensorLpExchange.Generic
