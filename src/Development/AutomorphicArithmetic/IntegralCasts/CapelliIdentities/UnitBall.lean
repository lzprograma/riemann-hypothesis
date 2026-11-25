module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BallRing
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.UnitBallLemmas.IsIntP :
    {p : ℕ} → [Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.UnitBallLemmas.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.UnitBallLemmas.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

private noncomputable def UpperTheory.Reformulated.B.UnitBallLemmas.unitBall (p : ℕ) [Fact (Nat.Prime p)] : Subring ℂ_[p] :=
  UpperTheory.Reformulated.B.ClosedUnitBallSubring.ballRing ℂ_[p]

theorem UpperTheory.Reformulated.B.UnitBallLemmas.intMv_inv.{u_1} :
    ∀ {p : ℕ} [Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.UnitBallLemmas.IntegralMv F →
        (MvPowerSeries.constantCoeff : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F = (1 : ℂ_[p]) →
          ∃ (G : MvPowerSeries σ ℂ_[p]), UpperTheory.Reformulated.B.UnitBallLemmas.IntegralMv G ∧ F * G = (1 : MvPowerSeries σ ℂ_[p]) := by
  intro p _ σ F hF h1
  let F' : MvPowerSeries σ (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p) :=
    fun n => ⟨MvPowerSeries.coeff n F, hF n⟩
  have hmap : MvPowerSeries.map (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p).subtype F' = F := by
    ext n
    rw [MvPowerSeries.coeff_map]
    rfl
  have hc : MvPowerSeries.constantCoeff F' = ((1 : (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p)ˣ) : UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p) := by
    apply Subtype.ext
    exact h1
  refine ⟨MvPowerSeries.map (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p).subtype (MvPowerSeries.invOfUnit F' 1), ?_, ?_⟩
  · intro n
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n (MvPowerSeries.invOfUnit F' 1)).2
  · rw [← hmap, ← map_mul, MvPowerSeries.mul_invOfUnit F' 1 hc, map_one]
