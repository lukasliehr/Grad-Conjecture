import AX12ZAmbient

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.AxisCore

open Grad.ClosedJets Grad.CartesianState
open Grad.ImplementationReadiness (VectorBlock spinPack)

/-- The smooth fourfold dense map, coordinatewise through the accepted
completion embedding. -/
def zEmbedding (parameters : PhaseParameters) (grade : ℕ) :
    (Fin 4 → GradeCore parameters 1 grade) →ₗ[ℂ] ZAmbient parameters grade where
  toFun cores := WithLp.toLp 2 (fun coordinate => aGradeEta parameters (cores coordinate))
  map_add' first second := by
    apply PiLp.ext
    intro coordinate
    exact (aGradeEta parameters).map_add (first coordinate) (second coordinate)
  map_smul' scalar cores := by
    apply PiLp.ext
    intro coordinate
    exact (aGradeEta parameters).map_smul scalar (cores coordinate)

theorem zEmbedding_apply (parameters : PhaseParameters) (grade : ℕ)
    (cores : Fin 4 → GradeCore parameters 1 grade) (coordinate : Fin 4) :
    zEmbedding parameters grade cores coordinate =
      aGradeEta parameters (cores coordinate) := rfl

/-- The inherited fourfold norm formula of the smooth embedding. -/
theorem zEmbedding_norm_sq (parameters : PhaseParameters) (grade : ℕ)
    (cores : Fin 4 → GradeCore parameters 1 grade) :
    ‖zEmbedding parameters grade cores‖ ^ 2 =
      ∑ coordinate : Fin 4, ‖cores coordinate‖ ^ 2 := by
  rw [zAmbient_norm_sq]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [zEmbedding_apply, (aGradeEta parameters).norm_map]

/-- The fourfold smooth embedding has dense range. -/
theorem zEmbedding_denseRange (parameters : PhaseParameters) (grade : ℕ) :
    DenseRange (zEmbedding parameters grade) := by
  rw [Metric.denseRange_iff]
  intro element epsilon positive
  have half : 0 < epsilon / 2 := by linarith
  choose approx close using fun coordinate : Fin 4 =>
    Metric.denseRange_iff.mp
      (aGradeEta_denseRange (dimension := 1) (grade := grade) parameters)
      (element coordinate) (epsilon / 2) half
  refine ⟨approx, ?_⟩
  rw [dist_eq_norm]
  have diffSq : ‖element - zEmbedding parameters grade approx‖ ^ 2 =
      ∑ coordinate : Fin 4,
        ‖element coordinate - aGradeEta parameters (approx coordinate)‖ ^ 2 := by
    rw [zAmbient_norm_sq]
    apply Finset.sum_congr rfl
    intro coordinate _
    rfl
  have termBound : ∀ coordinate : Fin 4,
      ‖element coordinate - aGradeEta parameters (approx coordinate)‖ ^ 2 <
        (epsilon / 2) ^ 2 := by
    intro coordinate
    have distance := close coordinate
    rw [dist_eq_norm] at distance
    have nonneg := norm_nonneg (element coordinate - aGradeEta parameters (approx coordinate))
    nlinarith
  have sumBound : (∑ coordinate : Fin 4,
      ‖element coordinate - aGradeEta parameters (approx coordinate)‖ ^ 2) <
        epsilon ^ 2 := by
    calc (∑ coordinate : Fin 4,
        ‖element coordinate - aGradeEta parameters (approx coordinate)‖ ^ 2)
        < ∑ _coordinate : Fin 4, (epsilon / 2) ^ 2 :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
            (fun coordinate _ => termBound coordinate)
      _ = epsilon ^ 2 := by
          rw [Fin.sum_univ_four]
          ring
  calc ‖element - zEmbedding parameters grade approx‖
      = Real.sqrt (‖element - zEmbedding parameters grade approx‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ < Real.sqrt (epsilon ^ 2) := by
        apply Real.sqrt_lt_sqrt (sq_nonneg _)
        rw [diffSq]
        exact sumBound
    _ = epsilon := Real.sqrt_sq positive.le

/-- The checked spin packing norm identity, instantiated at the actual
complex Hilbert `AGrade`: the squared vector weight is exactly two. -/
theorem zSpinPack_norm_sq (parameters : PhaseParameters) (grade : ℕ)
    (planar : VectorBlock (AGrade parameters 1 grade))
    (third fourth : AGrade parameters 1 grade) :
    ‖(spinPack planar third fourth : ZAmbient parameters grade)‖ ^ 2 =
      2 * ‖planar‖ ^ 2 + ‖third‖ ^ 2 + ‖fourth‖ ^ 2 :=
  Grad.ImplementationReadiness.spinPack_norm_sq planar third fourth

end Grad.AxisCore
