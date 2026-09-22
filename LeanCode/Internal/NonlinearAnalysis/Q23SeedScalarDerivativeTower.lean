import Q23SeedFieldDerivativeTower

noncomputable section

set_option maxRecDepth 6000
set_option maxHeartbeats 4000000

open Set
open scoped BigOperators ContDiff

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Gauges Grad.Constraints.Seed Grad.NonlinearProduct

/-- Curried real-bilinear form of the completed seed energy product. -/
def q23SeedEnergyBilinearCompletedCurried (phase : PhaseParameters) (grade : ℕ) :
    AGrade phase 3 (grade + 5) →L[ℝ]
      AGrade phase 3 (grade + 5) →L[ℝ] AGrade phase 1 (grade + 1) :=
  (continuousMultilinearCurryFin1 ℝ (AGrade phase 3 (grade + 5))
      (AGrade phase 1 (grade + 1))).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (completedSeedEnergyBilinear phase grade).curryLeft

theorem q23SeedEnergyBilinearCompletedCurried_apply
    (phase : PhaseParameters) (grade : ℕ)
    (first second : AGrade phase 3 (grade + 5)) :
    q23SeedEnergyBilinearCompletedCurried phase grade first second =
      completedSeedEnergyBilinear phase grade ![first, second] := by
  change completedSeedEnergyBilinear phase grade
      (Fin.cons first (Fin.snoc 0 second)) =
    completedSeedEnergyBilinear phase grade ![first, second]
  congr
  funext position
  exact Fin.eq_zero position ▸ rfl

/-- Binary-allocation core formula for derivatives of the quadratic seed
energy before subtracting the fixed radius-square field. -/
def q23SeedEnergyDiagonalCoreDerivative (phase : PhaseParameters) (order : ℕ)
    (parameter : Seed.Parameters) (directions : Fin order → Seed.Parameters) :
    ACore phase 1 :=
  ∑ assignment : Fin order → Fin 2,
    seedEnergyBilinearCore phase ![
      q23SeedFieldCoreDerivative phase (assignmentFiber assignment 0).card parameter
        (q23FiberTuple assignment 0 directions),
      q23SeedFieldCoreDerivative phase (assignmentFiber assignment 1).card parameter
        (q23FiberTuple assignment 1 directions)]

theorem completedSeedEnergyDiagonal_all_orders_core
    (phase : PhaseParameters) (grade order : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    iteratedFDeriv ℝ order
        (fun point => completedSeedEnergyBilinear phase grade
          (fun _ => completedTameSeedFieldFamily phase (grade + 5) point))
        parameter directions =
      q23FieldEmbed phase 1 (grade + 1)
        (q23SeedEnergyDiagonalCoreDerivative phase order parameter directions) := by
  have allocation := iteratedFDeriv_bilinear_allocation_all_orders
    (q23SeedEnergyBilinearCompletedCurried phase grade)
    (completedTameSeedFieldFamily phase (grade + 5))
    (completedTameSeedFieldFamily phase (grade + 5))
    Seed.parameterDomain Seed.parameterDomain_isOpen
    (completedTameSeedFieldFamily_contDiffOn phase (grade + 5))
    (completedTameSeedFieldFamily_contDiffOn phase (grade + 5))
    order parameter inside directions
  change iteratedFDeriv ℝ order
      (fun point => q23SeedEnergyBilinearCompletedCurried phase grade
        (completedTameSeedFieldFamily phase (grade + 5) point)
        (completedTameSeedFieldFamily phase (grade + 5) point))
      parameter directions = _ at allocation
  have familyEquality :
      (fun point => completedSeedEnergyBilinear phase grade
        (fun _ => completedTameSeedFieldFamily phase (grade + 5) point)) =
      (fun point => q23SeedEnergyBilinearCompletedCurried phase grade
        (completedTameSeedFieldFamily phase (grade + 5) point)
        (completedTameSeedFieldFamily phase (grade + 5) point)) := by
    funext point
    rw [q23SeedEnergyBilinearCompletedCurried_apply]
    congr
    funext position
    fin_cases position <;> rfl
  rw [familyEquality, allocation]
  unfold q23SeedEnergyDiagonalCoreDerivative
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro assignment _
  rw [completedTameSeedFieldFamily_all_orders_core phase (grade + 5)
      (assignmentFiber assignment 0).card parameter inside,
    completedTameSeedFieldFamily_all_orders_core phase (grade + 5)
      (assignmentFiber assignment 1).card parameter inside,
    q23SeedEnergyBilinearCompletedCurried_apply]
  let fields : Fin 2 → ACore phase 3 :=
    ![q23SeedFieldCoreDerivative phase (assignmentFiber assignment 0).card parameter
        (q23FiberTuple assignment 0 directions),
      q23SeedFieldCoreDerivative phase (assignmentFiber assignment 1).card parameter
        (q23FiberTuple assignment 1 directions)]
  have core := completedSeedEnergyBilinear_core phase grade fields
  have argumentEquality :
      ![q23ACoreEta phase 3 (grade + 5)
          (q23SeedFieldCoreDerivative phase (assignmentFiber assignment 0).card parameter
            (q23FiberTuple assignment 0 directions)),
        q23ACoreEta phase 3 (grade + 5)
          (q23SeedFieldCoreDerivative phase (assignmentFiber assignment 1).card parameter
            (q23FiberTuple assignment 1 directions))] =
      fun position => q23FieldEmbed phase 3 (grade + 5) (fields position) := by
    funext position
    fin_cases position
    · rfl
    · rfl
  rw [argumentEquality]
  simpa only [fields] using core

def q23CoreConstantValueDerivative {E : Type*} [AddCommMonoid E]
    (value : E) (order : ℕ) : E :=
  if order = 0 then value else 0

theorem iteratedFDeriv_const_value_core
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (value : F) (order : ℕ) (point : E) (directions : Fin order → E) :
    iteratedFDeriv ℝ order (fun _ : E => value) point directions =
      q23CoreConstantValueDerivative value order := by
  cases order with
  | zero => rfl
  | succ order =>
      rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero order) value]
      simp [q23CoreConstantValueDerivative]

def q23SeedEnergyCoreDerivative (phase : PhaseParameters) (order : ℕ)
    (parameter : Seed.Parameters) (directions : Fin order → Seed.Parameters) :
    ACore phase 1 :=
  q23SeedEnergyDiagonalCoreDerivative phase order parameter directions -
    q23CoreConstantValueDerivative (tameRadiusSquareField phase) order

theorem completedTameSeedEnergyFamily_all_orders_core
    (phase : PhaseParameters) (grade order : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    iteratedFDeriv ℝ order (completedTameSeedEnergyFamily phase grade)
        parameter directions =
      q23FieldEmbed phase 1 (grade + 1)
        (q23SeedEnergyCoreDerivative phase order parameter directions) := by
  have diagonalOn : ContDiffOn ℝ ∞
      (fun point => completedSeedEnergyBilinear phase grade
        (fun _ => completedTameSeedFieldFamily phase (grade + 5) point))
      Seed.parameterDomain := by
    have diagonal : ContDiffOn ℝ ∞
        (fun point : Seed.Parameters => fun _ : Fin 2 =>
          completedTameSeedFieldFamily phase (grade + 5) point)
        Seed.parameterDomain :=
      contDiffOn_pi.2
        (fun _ => completedTameSeedFieldFamily_contDiffOn phase (grade + 5))
    exact (completedSeedEnergyBilinear phase grade).contDiff.comp_contDiffOn diagonal
  have diagonalSmooth : ContDiffAt ℝ ∞
      (fun point => completedSeedEnergyBilinear phase grade
        (fun _ => completedTameSeedFieldFamily phase (grade + 5) point)) parameter :=
    diagonalOn.contDiffAt (Seed.parameterDomain_isOpen.mem_nhds inside)
  have constantSmooth : ContDiffAt ℝ ∞
      (fun _ : Seed.Parameters =>
        q23FieldEmbed phase 1 (grade + 1) (tameRadiusSquareField phase)) parameter :=
    contDiffAt_const
  change (iteratedFDeriv ℝ order
      ((fun point => completedSeedEnergyBilinear phase grade
          (fun _ => completedTameSeedFieldFamily phase (grade + 5) point)) -
        (fun _ : Seed.Parameters =>
          q23FieldEmbed phase 1 (grade + 1) (tameRadiusSquareField phase)))
      parameter) directions = _
  rw [iteratedFDeriv_sub_apply
    (diagonalSmooth.of_le (show (order : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
    (constantSmooth.of_le (show (order : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))]
  simp only [sub_apply]
  rw [
    completedSeedEnergyDiagonal_all_orders_core phase grade order parameter inside,
    iteratedFDeriv_const_value_core]
  unfold q23SeedEnergyCoreDerivative
  rw [map_sub]
  cases order <;> simp [q23CoreConstantValueDerivative]

/-- Core representative of every seed derivative of the literal Q17 scalar. -/
def q23SeedScalarCoreDerivative (phase : PhaseParameters) (order : ℕ)
    (parameter : Seed.Parameters) (directions : Fin order → Seed.Parameters) :
    ACore phase 1 :=
  (-(4 : ℂ)⁻¹) • rotationCore phase
    (q23SeedEnergyCoreDerivative phase order parameter directions)

theorem completedTameSeedScalarFamily_all_orders_core
    (phase : PhaseParameters) (grade order : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    iteratedFDeriv ℝ order (completedTameSeedScalarFamily phase grade)
        parameter directions =
      q23FieldEmbed phase 1 grade
        (q23SeedScalarCoreDerivative phase order parameter directions) := by
  let rotationReal : AGrade phase 1 (grade + 1) →L[ℝ] AGrade phase 1 grade :=
    (q23RotationCompletedLossOne phase grade).restrictScalars ℝ
  let scalarReal : AGrade phase 1 grade →L[ℝ] AGrade phase 1 grade :=
    q23ComplexScalarCLM (E := AGrade phase 1 grade) (-(4 : ℂ)⁻¹)
  let post : AGrade phase 1 (grade + 1) →L[ℝ] AGrade phase 1 grade :=
    scalarReal.comp rotationReal
  have energySmooth :=
    (completedTameSeedEnergyFamily_contDiffOn phase grade).contDiffAt
      (Seed.parameterDomain_isOpen.mem_nhds inside)
  have mapped := q23IteratedFDeriv_linearFunction_comp
    (fun energy : AGrade phase 1 (grade + 1) => post energy)
    post.map_add post.map_smul post.continuous
    (completedTameSeedEnergyFamily phase grade) parameter energySmooth order directions
  have familyEquality : completedTameSeedScalarFamily phase grade =
      fun point => post (completedTameSeedEnergyFamily phase grade point) := by
    funext point
    rfl
  rw [familyEquality]
  rw [mapped,
    completedTameSeedEnergyFamily_all_orders_core phase grade order parameter inside]
  change (-(4 : ℂ)⁻¹) • q23RotationCompletedLossOne phase grade
      (q23FieldEmbed phase 1 (grade + 1)
        (q23SeedEnergyCoreDerivative phase order parameter directions)) = _
  rw [q23RotationCompletedLossOne_core]
  unfold q23SeedScalarCoreDerivative
  rw [map_smul]

end Grad.NonlinearQuotientBounds
