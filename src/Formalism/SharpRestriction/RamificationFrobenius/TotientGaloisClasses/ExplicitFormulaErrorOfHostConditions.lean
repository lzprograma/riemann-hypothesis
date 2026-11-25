module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Analytic
public import Formalism.StatementOC
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace Formalism.HC

structure Level extends KSet where
  o : ℕ

def PChar.ZeroFreeAbove (ψ : PChar) (θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction ψ.χ s ≠ 0

def ZeroFreeOn (Q : PChar → Prop) : Prop := ∀ ψ : PChar, Q ψ → ψ.ZeroFreeAbove (1 / 2)

def ZeroFreeAll : Prop := ZeroFreeOn fun _ => True

namespace Level

variable (Λ : Level)

def ZeroFreeAbove (θ : ℝ) : Prop := ∀ ψ ∈ Λ.KEPT, ψ.ZeroFreeAbove θ

def ZeroFreeLevel : Prop := Λ.ZeroFreeAbove (1 / 2)


open Classical in
def Nt : Finset PChar := Λ.KEPT.erase PChar.one


open Classical in
def wt (ψ : PChar) : ℝ := if Λ.psK = some ψ then 1 else (3 * (Λ.o : ℝ) + 1)⁻¹

def Gm (y : ℝ) : ℝ := Formalism.Gz y + ∑ ψ ∈ Λ.Nt, Λ.wt ψ * (An.gChi ψ.χ y).re

end Level

theorem zeroFreeOn_of_levels {Q : PChar → Prop} (h : ∀ ψ, Q ψ → ∃ Λ : Level, ψ ∈ Λ.KEPT ∧ Λ.ZeroFreeLevel) : ZeroFreeOn Q := by
  intro ψ hψ
  obtain ⟨Λ, h1, h2⟩ := h ψ hψ
  exact h2 ψ h1

private theorem pchar_mk_eq_of_changeLevel_eq_self_of_primitive {N d : ℕ} [NeZero N] [NeZero d] (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ d) (hd : d ∣ N) (hc : DirichletCharacter.changeLevel hd ψ = χ)
    (h1 : ψ.IsPrimitive) (h2 : χ.IsPrimitive) (he : d = N) :
    PChar.mk d ψ h1 = PChar.mk N χ h2 := by
  subst he
  rw [DirichletCharacter.changeLevel_self] at hc
  subst hc
  rfl

theorem PChar.of_self (ψ : PChar) : PChar.of ψ.χ = ψ := by
  haveI : NeZero ψ.χ.conductor := ⟨ψ.χ.conductor_ne_zero⟩
  exact pchar_mk_eq_of_changeLevel_eq_self_of_primitive ψ.χ ψ.χ.primitiveCharacter ψ.χ.conductor_dvd_level
    ψ.χ.changeLevel_primitiveCharacter ψ.χ.primitiveCharacter_isPrimitive ψ.prim ψ.prim

private theorem pchar_mk_eq_one_of_level_eq_one {d : ℕ} [NeZero d] (ψ : DirichletCharacter ℂ d) (h : ψ.IsPrimitive)
    (he : d = 1) : PChar.mk d ψ h = PChar.one := by
  subst he
  obtain rfl := DirichletCharacter.level_one ψ
  rfl

theorem PChar.of_one (M : ℕ) [NeZero M] : PChar.of (1 : DirichletCharacter ℂ M) = PChar.one := by
  haveI : NeZero (1 : DirichletCharacter ℂ M).conductor :=
    ⟨(1 : DirichletCharacter ℂ M).conductor_ne_zero⟩
  exact pchar_mk_eq_one_of_level_eq_one _ _ DirichletCharacter.conductor_one


open Classical in
def Level.ofSub {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) : Level where
  KEPT := (Finset.univ.filter fun χ : DirichletCharacter ℂ M => χ ∈ Ξ).image PChar.of
  one_mem := Finset.mem_image.2 ⟨1, Finset.mem_filter.2 ⟨Finset.mem_univ _, Ξ.one_mem⟩, PChar.of_one M⟩
  psK := none
  o := Nat.card Ξ

theorem Level.mem_ofSub {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (ψ : PChar) :
    ψ ∈ (Level.ofSub Ξ).KEPT ↔ ∃ χ ∈ Ξ, PChar.of χ = ψ := by
  classical
  simp [Level.ofSub]

def Level.cyc (ψ : PChar) : Level := Level.ofSub (Subgroup.zpowers ψ.χ)

theorem Level.mem_cyc (ψ : PChar) : ψ ∈ (Level.cyc ψ).KEPT :=
  (Level.mem_ofSub _ _).2 ⟨ψ.χ, Subgroup.mem_zpowers _, ψ.of_self⟩

namespace Frame

variable (φ : Frame)


open Classical in
def lam (γ : φ.A) : ℝ := (if γ ∈ φ.A0 then 4 else 3) / (3 * (φ.o : ℝ) + 1)


open Classical in
def Shares (TT : Finset φ.A) (δ : ℝ) : Prop :=
  ∀ γ : φ.A, |((TT.filter fun t => t - γ ∈ φ.A0).card : ℝ) - φ.lam γ * (TT.card : ℝ)| ≤ δ * (TT.card : ℝ)

end Frame

structure EAtH (Λ : Level) {φ : Frame} (H : HostRaw φ) (TT : Finset φ.A) (x eps C : ℝ) : Prop where
  o_eq : φ.o = Λ.o
  kept : H.KeptInXp Λ.KEPT
  ps : H.ExceptionalCharacterKept Λ.KEPT Λ.psK
  shares : φ.Shares TT (x ^ (-1 + eps))
  bdG : H.BoundedCharsPointwise Λ.KEPT x eps
  bdL : ∀ θ ∈ H.Bounded Λ.KEPT, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf θ χ →
    ‖An.logDerivativeAtOne χ‖ ≤ C * Real.log x

end Formalism.HC

end
