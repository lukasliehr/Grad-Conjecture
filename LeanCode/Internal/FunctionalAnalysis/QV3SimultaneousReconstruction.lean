import QV2AllGradeExtension

noncomputable section

namespace Grad.ConstrainedGrades

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.RealFixedRanges
open Grad.AxisCore Grad.SmoothingFamily Grad.CompatibleCompletion Grad.QuotientProjection

theorem stateAxis_coefficient_common (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (family : CompatibleStates parameters parameter inside)
    (grade : ℕ) (cell : ℤ) :
    Grad.AxisCore.axisCoefficient parameters (grade + 1)
      (extendedState parameters parameter inside family grade).ofLp.1 cell =
    Grad.AxisCore.axisCoefficient parameters 1
      (extendedState parameters parameter inside family 0).ofLp.1 cell := by
  have compatible := congrArg (fun field : XAmbient parameters 0 => field.ofLp.1)
    (extendedState_compatible parameters parameter inside family 0 grade (Nat.zero_le grade))
  change axisLowering parameters (Nat.add_le_add_right (Nat.zero_le grade) 1)
    (extendedState parameters parameter inside family grade).ofLp.1 =
      (extendedState parameters parameter inside family 0).ofLp.1 at compatible
  simpa only [axisLowering_coefficient] using congrArg
    (fun field => Grad.AxisCore.axisCoefficient parameters 1 field cell) compatible

/-- One literal common coefficient sequence, proved to belong to every
axis grade. Its coefficients are not chosen separately at different grades. -/
def reconstructedAxis (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (family : CompatibleStates parameters parameter inside) :
    Grad.SmoothingFamily.AxisCore parameters.sigma0 (ComplexEuclidean 2) :=
  ⟨fun cell => Grad.AxisCore.axisCoefficient parameters 1
      (extendedState parameters parameter inside family 0).ofLp.1 cell, by
    intro grade
    let candidate := axisLowering parameters (Nat.le_succ grade)
      (extendedState parameters parameter inside family grade).ofLp.1
    have member := lp.memℓp candidate
    convert member using 1
    funext cell
    change (Grad.AxisCore.axisWeight parameters grade cell : ℂ) •
        Grad.AxisCore.axisCoefficient parameters 1
          (extendedState parameters parameter inside family 0).ofLp.1 cell =
      (Grad.AxisCore.axisWeight parameters grade cell : ℂ) •
        Grad.AxisCore.axisCoefficient parameters (grade + 1)
          (extendedState parameters parameter inside family grade).ofLp.1 cell
    exact congrArg (fun vector => (Grad.AxisCore.axisWeight parameters grade cell : ℂ) • vector)
      (stateAxis_coefficient_common parameters parameter inside family grade cell).symm⟩

theorem reconstructedAxis_grade (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (family : CompatibleStates parameters parameter inside)
    (grade : ℕ) :
    Grad.SmoothingFamily.axisToGrade parameters.sigma0 (grade + 1)
      (reconstructedAxis parameters parameter inside family) =
        (extendedState parameters parameter inside family grade).ofLp.1 := by
  apply axisCoefficient_ext parameters
  intro cell
  change Grad.SmoothingFamily.axisCoefficient parameters.sigma0 (grade + 1)
    (Grad.SmoothingFamily.axisToGrade parameters.sigma0 (grade + 1)
      (reconstructedAxis parameters parameter inside family)) cell = _
  rw [Grad.SmoothingFamily.axisToGrade_coefficient]
  exact (stateAxis_coefficient_common parameters parameter inside family grade cell).symm

def stateVectorFamily (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (family : CompatibleStates parameters parameter inside) :
    CompatibleAGrades parameters 3 :=
  ⟨fun grade => (extendedState parameters parameter inside family grade).ofLp.2.ofLp.1, by
    intro lower upper ordered
    exact congrArg (fun field : XAmbient parameters lower => field.ofLp.2.ofLp.1)
      (extendedState_compatible parameters parameter inside family lower upper ordered)⟩

def stateScalarFamily (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (family : CompatibleStates parameters parameter inside) :
    CompatibleAGrades parameters 1 :=
  ⟨fun grade => (extendedState parameters parameter inside family grade).ofLp.2.ofLp.2, by
    intro lower upper ordered
    exact congrArg (fun field : XAmbient parameters lower => field.ofLp.2.ofLp.2)
      (extendedState_compatible parameters parameter inside family lower upper ordered)⟩

def sourceComponentFamily (parameters : PhaseParameters) (family : CompatibleSources parameters)
    (coordinate : Fin 4) : CompatibleAGrades parameters 1 :=
  ⟨fun grade => extendedSource parameters family grade coordinate, by
    intro lower upper ordered
    exact congrArg (fun field : ZAmbient parameters lower => field coordinate)
      (extendedSource_compatible parameters family lower upper ordered)⟩

/-- A single actual smooth ambient triple reconstructed simultaneously
through the accepted COR16 field reconstruction and common axis sequence. -/
def reconstructedState (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (family : CompatibleStates parameters parameter inside) :
    StateCore parameters :=
  (reconstructedAxis parameters parameter inside family,
    compatibleToCore parameters (stateVectorFamily parameters parameter inside family),
    compatibleToCore parameters (stateScalarFamily parameters parameter inside family))

def reconstructedSource (parameters : PhaseParameters) (family : CompatibleSources parameters) :
    SmoothQuotient parameters :=
  fun coordinate => compatibleToCore parameters (sourceComponentFamily parameters family coordinate)

theorem reconstructedState_grade (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (family : CompatibleStates parameters parameter inside)
    (grade : ℕ) : stateToGrade parameters grade (reconstructedState parameters parameter inside family) =
      extendedState parameters parameter inside family grade := by
  apply (WithLp.equiv 1 _).injective
  apply Prod.ext
  · exact reconstructedAxis_grade parameters parameter inside family grade
  · apply (WithLp.equiv 1 _).injective
    exact Prod.ext (compatibleToCore_component parameters (stateVectorFamily parameters parameter inside family) grade)
      (compatibleToCore_component parameters (stateScalarFamily parameters parameter inside family) grade)

theorem reconstructedSource_grade (parameters : PhaseParameters) (family : CompatibleSources parameters)
    (grade : ℕ) : quotientEta parameters grade (reconstructedSource parameters family) =
      extendedSource parameters family grade := by
  apply PiLp.ext
  intro coordinate
  exact compatibleToCore_component parameters (sourceComponentFamily parameters family coordinate) grade

end Grad.ConstrainedGrades
