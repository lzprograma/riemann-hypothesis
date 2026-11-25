module

public import Formalism.LocalRingCardinality.DataHost
public import Mathlib.Analysis.CStarAlgebra.Classes
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField Matrix
open scoped ComplexOrder

variable {R : Ranks}

abbrev Pl (R : Ranks) : Type := ↥(R.Psi)

instance instFintypePl : Fintype (Pl R) := Fintype.ofFinite _

def tau (H : Host R) (τ : Pl R) : H.E →+* ℂ := H.emb τ.1

theorem conj_conj (H : Host R) (x : H.E) : H.conj (H.conj x) = x :=
  H.φ₀.injective (by
    rw [show H.φ₀ (H.conj (H.conj x)) = _ from H.conjE_apply _ _,
      show H.φ₀ (H.conj x) = _ from H.conjE_apply _ _]
    simp)

abbrev V (H : Host R) (n : ℕ) : Type := Fin n → H.E

variable {H : Host R} {n : ℕ}

theorem smul_dot (a : 𝓞 H.E) (y x : V H n) : (a • y) ⬝ᵥ x = y ⬝ᵥ (a • x) := by
  rw [smul_dotProduct, dotProduct_smul]

def dualZ (X : Submodule (𝓞 H.E) (V H n)) : Submodule (𝓞 H.E) (V H n) where
  carrier := {y | ∀ x ∈ X, ∃ z : ℤ, Algebra.trace ℚ H.E (y ⬝ᵥ x) = z}
  add_mem' := fun {y y'} hy hy' x hx => by
    obtain ⟨z, h⟩ := hy x hx
    obtain ⟨z', h'⟩ := hy' x hx
    exact ⟨z + z', by rw [add_dotProduct, map_add (f := _), h, h']; push_cast; rfl⟩
  zero_mem' := fun x _ => ⟨0, by simp⟩
  smul_mem' := fun a y hy x hx => by rw [smul_dot]; exact hy _ (X.smul_mem a hx)

def Herm (H : Host R) (n : ℕ) : Submodule ℚ (Matrix (Fin n) (Fin n) H.E) where
  carrier := {χ | ∀ i k, χ k i = H.conj (χ i k)}
  add_mem' := fun {a b} ha hb i k => by simp [ha i k, hb i k]
  zero_mem' := fun i k => by simp
  smul_mem' := fun q a ha i k => by
    simp only [Matrix.smul_apply, ha i k, Rat.smul_def, map_mul, map_ratCast]

abbrev XR (R : Ranks) (n : ℕ) : Type := Pl R → Fin n → ℂ

def act (a : H.E) (u : XR R n) : XR R n := fun τ i => tau H τ a * u τ i

def Bal (H : Host R) (n : ℕ) : Submodule ℝ (XR R n →ₗ[ℝ] XR R n →ₗ[ℝ] ℝ) where
  carrier := {B | (∀ u v, B u v = B v u) ∧
    ∀ (a : 𝓞 H.E) u v, B (act (a : H.E) u) v = B u (act (H.conj (a : H.E)) v)}
  add_mem' := by
    rintro B C ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨fun u v => by simp [h1 u v, h3 u v], fun a u v => by simp [h2 a u v, h4 a u v]⟩
  zero_mem' := by simp
  smul_mem' := by
    rintro t B ⟨h1, h2⟩
    exact ⟨fun u v => by simp [h1 u v], fun a u v => by simp [h2 a u v]⟩

def bil (B : Bal H n) (u v : XR R n) : ℝ := (B : XR R n →ₗ[ℝ] XR R n →ₗ[ℝ] ℝ) u v

def Q (B : Bal H n) (u : XR R n) : ℝ := bil B u u / 2


open Classical in
def vec (τ : Pl R) (i : Fin n) (z : ℂ) : XR R n := Pi.single τ (Pi.single i z)

end GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents

end
