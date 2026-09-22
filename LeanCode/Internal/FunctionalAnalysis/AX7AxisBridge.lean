import AX6AxisConsumer
import SM15StateCarrier

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.AxisCore

open Grad.ClosedJets Grad.CartesianState

/-- The accepted smoothing axis weight at the original width is literally
this lane's axis weight. -/
theorem bridge_weight (parameters : PhaseParameters) (grade : ℕ) (cell : ℤ) :
    Grad.SmoothingFamily.axisWeight parameters.sigma0 grade cell =
      axisWeight parameters grade cell := rfl

/-- The accepted smoothing carrier at the planar value space is literally
this lane's axis carrier. -/
theorem bridge_carrier (parameters : PhaseParameters) (grade : ℕ) :
    Grad.SmoothingFamily.TGrade parameters.sigma0 (ComplexEuclidean 2) grade =
      AxisGrade parameters 2 grade := rfl

/-- This lane's all-grade axis smooth core lands in the accepted smoothing
axis core, with the same coefficient family. -/
def bridgeCore (parameters : PhaseParameters) (family : AxisSmoothCore parameters 2) :
    Grad.SmoothingFamily.AxisCore parameters.sigma0 (ComplexEuclidean 2) :=
  ⟨family.1, by
    show ∀ grade : ℕ, Memℓp
      (fun cell => (axisWeight parameters grade cell : ℂ) • family.1 cell) 2
    intro grade
    rw [memlp_iff_summable_sq]
    apply ((family.2 grade).congr)
    intro cell
    show axisWeight parameters grade cell ^ 2 * ‖family.1 cell‖ ^ 2 =
      ‖(axisWeight parameters grade cell : ℂ) • family.1 cell‖ ^ 2
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (axisWeight_pos parameters grade cell), mul_pow]⟩

/-- The accepted grade embedding of the bridged core is literally this
lane's same-coefficient embedding. -/
theorem bridgeCore_toGrade (parameters : PhaseParameters) (grade : ℕ)
    (family : AxisSmoothCore parameters 2) :
    Grad.SmoothingFamily.axisToGrade parameters.sigma0 grade
        (bridgeCore parameters family) =
      axisEta parameters 2 grade family := by
  apply lp.ext
  funext cell
  rfl

end Grad.AxisCore
