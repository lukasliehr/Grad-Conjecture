import ANH10DiskFourierEnergy
import GQC30APSmoothFaithfulness

noncomputable section

set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.CircularHighWeak

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated

def closedL2Core : ClosedJet 1 →ₗ[ℂ] DiskL2 1 where
  toFun field := closedContinuousToDiskL2 field.value
  map_add' first second := by
    rw [closedJet_value_add, closedContinuousToDiskL2_add]
  map_smul' scalar field := by
    rw [closedJet_value_smul, closedContinuousToDiskL2_smul]
    rfl

theorem closedL2Core_injective : Function.Injective closedL2Core := by
  intro first second equality
  apply closedJet_eq_of_value_eq
  exact closedValueL2_injective 1 equality

/-- Smooth closed jets are dense in the actual full-disk L2, by the
accepted compact Cartesian test separation theorem. -/
theorem closedL2Core_denseRange : DenseRange closedL2Core := by
  let closure := closedL2Core.range.topologicalClosure
  have orthogonalZero : closureᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro field orthogonal
    change field = 0
    have coordinateZero : ∀ᵐ point ∂volume.restrict openUnitDisk, field point 0 = 0 := by
      have locally : LocallyIntegrable (fun point => field point 0) (volume.restrict openUnitDisk) :=
        ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).comp_memLp field).locallyIntegrable (by norm_num)
      have zeroOn : ∀ᵐ point ∂volume.restrict openUnitDisk,
          point ∈ openUnitDisk → field point 0 = 0 := by
        apply openUnitDisk_isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
          (locally.locallyIntegrableOn openUnitDisk)
        intro test smooth _compact _supported
        let vector : PhysicalValue 1 := EuclideanSpace.single 0 1
        let core := globalClosedJet (fun point => test point • vector) (smooth.smul contDiff_const)
        have pairing : inner ℂ (closedL2Core core) field = 0 :=
          (closure.mem_orthogonal field).mp orthogonal _
            (Submodule.le_topologicalClosure _ ⟨core, rfl⟩)
        rw [L2.inner_def] at pairing
        have equality : (∫ point in openUnitDisk, inner ℂ (closedL2Core core point) (field point)) =
            ∫ point in openUnitDisk, test point • field point 0 := by
          apply integral_congr_ae
          filter_upwards [closedContinuousToDiskL2_ae core.value,
            ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point literal inside
          change inner ℂ (closedContinuousToDiskL2 core.value point) (field point) = _
          rw [literal, closedDiskLift, dif_pos (openDiskMembershipClosed point inside)]
          change inner ℂ (test point • vector) (field point) = _
          rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (test point) vector, inner_smul_real_left]
          simp only [vector, EuclideanSpace.inner_single_left, map_one, one_mul]
        exact equality.symm.trans pairing
      filter_upwards [zeroOn, ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point zero inside
      exact zero inside
    apply Lp.ext
    filter_upwards [coordinateZero, Lp.coeFn_zero (PhysicalValue 1) 2 (volume.restrict openUnitDisk)]
      with point zero zeroValue
    rw [zeroValue]
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate
    exact zero
  have full : closure = ⊤ := Submodule.orthogonal_eq_bot_iff.mp orthogonalZero
  have dense : Dense (closedL2Core.range : Set (DiskL2 1)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr full
  exact dense

end Grad.CircularHighWeak
