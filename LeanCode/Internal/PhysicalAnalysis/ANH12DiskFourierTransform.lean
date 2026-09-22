import ANH11DiskL2Density

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal

namespace Grad.CircularHighWeak

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger

abbrev DiskFourier := lp (fun _ : ℤ => DiskL2 1) 2

def coreDiskFourier : ClosedJet 1 →ₗ[ℂ] DiskFourier where
  toFun field := ⟨fun mode => closedL2Core (angularClosedJet mode field), by
    change Memℓp (fun mode => closedL2Core (angularClosedJet mode field)) 2
    rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
    simpa [closedL2Core] using diskMode_summable_sq field⟩
  map_add' first second := by
    apply lp.ext
    funext mode
    change closedL2Core (angularClosedJetLinear 1 mode (first + second)) = _
    rw [map_add, map_add]
    rfl
  map_smul' scalar field := by
    apply lp.ext
    funext mode
    change closedL2Core (angularClosedJetLinear 1 mode (scalar • field)) = _
    rw [map_smul, map_smul]
    rfl

theorem coreDiskFourier_norm (field : ClosedJet 1) :
    ‖coreDiskFourier field‖ = ‖closedL2Core field‖ := by
  have normLaw := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (coreDiskFourier field)
  norm_num at normLaw
  have squared := normLaw.trans (diskMode_parseval field)
  have rooted := congrArg Real.sqrt squared
  simp only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at rooted
  exact rooted

theorem diskFourier_exists : ∃ transform : DiskL2 1 →L[ℂ] DiskFourier,
    (∀ core, transform (closedL2Core core) = coreDiskFourier core) ∧
      ∀ field, ‖transform field‖ ≤ ‖field‖ := by
  obtain ⟨transform, core, bound⟩ := apDense_extension (closedL2Core)
    closedL2Core_injective closedL2Core_denseRange coreDiskFourier 1 zero_le_one (by
      intro field
      rw [one_mul, coreDiskFourier_norm])
  exact ⟨transform, core, fun field => (bound field).trans_eq (one_mul _)⟩

/-- Angular Fourier decomposition on the actual disk L2, with disk-valued
mode components and ordinary area normalization. -/
def diskFourier : DiskL2 1 →L[ℂ] DiskFourier := diskFourier_exists.choose

theorem diskFourier_core (field : ClosedJet 1) :
    diskFourier (closedL2Core field) = coreDiskFourier field :=
  diskFourier_exists.choose_spec.1 field

theorem diskFourier_norm (field : DiskL2 1) : ‖diskFourier field‖ = ‖field‖ := by
  apply isClosed_property closedL2Core_denseRange
    (isClosed_eq diskFourier.continuous.norm continuous_norm) _ field
  intro core
  exact (congrArg norm (diskFourier_core core)).trans (coreDiskFourier_norm core)

def diskFourierIsometry : DiskL2 1 →ₗᵢ[ℂ] DiskFourier where
  toLinearMap := diskFourier.toLinearMap
  norm_map' := diskFourier_norm

def diskMode (mode : ℤ) : DiskL2 1 →L[ℂ] DiskL2 1 :=
  (lp.evalCLM ℂ (fun _ : ℤ => DiskL2 1) 2 mode).comp diskFourier

theorem diskMode_core (mode : ℤ) (field : ClosedJet 1) :
    diskMode mode (closedL2Core field) =
      closedL2Core (angularClosedJet mode field) := by
  change diskFourier (closedL2Core field) mode = _
  rw [diskFourier_core]
  rfl

theorem diskMode_projection (first second : ℤ) (field : DiskL2 1) :
    diskMode first (diskMode second field) =
      if first = second then diskMode first field else 0 := by
  apply isClosed_property closedL2Core_denseRange
    (isClosed_eq ((diskMode first).continuous.comp (diskMode second).continuous)
      (by split_ifs <;> fun_prop)) _ field
  intro core
  change diskMode first (diskMode second (closedL2Core core)) =
    if first = second then diskMode first (closedL2Core core) else 0
  rw [diskMode_core, diskMode_core, angularClosedJet_projection]
  split_ifs with equal
  · rw [diskMode_core]
  · exact map_zero _

theorem diskFourier_mode (mode : ℤ) (field : DiskL2 1) :
    diskFourier (diskMode mode field) = lp.single 2 mode (diskMode mode field) := by
  apply lp.ext
  funext other
  change diskMode other (diskMode mode field) = _
  rw [diskMode_projection, lp.single_apply]
  by_cases equal : other = mode
  · subst other
    simp
  · simp [equal]

end Grad.CircularHighWeak
