module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.Poinc.TwistSum₂

theorem sumI_of_sumF_mul {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] {Ix : Type}
    (y : Ix → V) (v : V) (d : FractionRing V) (hd : d ≠ 0)
    (h : SumF (maximalIdeal V) (FractionRing V) (fun i => algebraMap V (FractionRing V) (y i) * d)
      (algebraMap V (FractionRing V) v * d)) :
    SumI (maximalIdeal V) y v := by
  classical
  have hsm : ∀ (r : V) (x : FractionRing V), r • x = algebraMap V (FractionRing V) r * x := Algebra.smul_def
  have hmod : (Module.compHom (FractionRing V) (algebraMap V (FractionRing V)) : Module V (FractionRing V)) =
      Algebra.toModule := Module.ext' _ _ fun r x => (Algebra.smul_def r x).symm
  unfold SumF at h
  rw [hmod] at h
  obtain ⟨N, hN, -, -, hS⟩ := h
  let P : Submodule V (FractionRing V) := N ⊔ Submodule.span V {d}
  haveI : Module.Finite V P := Module.Finite.iff_fg.mpr (hN.sup (Submodule.fg_span_singleton d))
  let L : Submodule V P := (Submodule.span V {d}).comap P.subtype
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal V) L
  refine ⟨⊤, Module.Finite.fg_top, Submodule.mem_top, fun _ => Submodule.mem_top, fun n => ?_⟩
  obtain ⟨S, hS⟩ := hS (n + k)
  refine ⟨S, fun T hT => ?_⟩
  set w : V := v - ∑ i ∈ T, y i with hw
  have e : algebraMap V (FractionRing V) w * d =
      algebraMap V (FractionRing V) v * d - ∑ i ∈ T, algebraMap V (FractionRing V) (y i) * d := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hw, map_sub, map_sum, sub_mul, Finset.sum_mul]
  have h1 : algebraMap V (FractionRing V) w * d ∈ maximalIdeal V ^ (n + k) • N := e ▸ hS T hT
  have hwP : algebraMap V (FractionRing V) w * d ∈ P :=
    Submodule.mem_sup_right (by rw [← hsm]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d))
  let p : P := ⟨_, hwP⟩
  have hp1 : p ∈ maximalIdeal V ^ (n + k) • (⊤ : Submodule V P) :=
    (Submodule.mem_smul_top_iff _ P p).2 (Submodule.smul_mono le_rfl le_sup_left h1)
  have hp2 : p ∈ L := by
    show algebraMap V (FractionRing V) w * d ∈ Submodule.span V {d}
    rw [← hsm]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d)
  have hp3 : p ∈ maximalIdeal V ^ n • L := by
    have := (hk (n + k) (Nat.le_add_left _ _)).le ⟨hp1, hp2⟩
    rw [Nat.add_sub_cancel] at this
    exact Submodule.smul_mono le_rfl inf_le_right this
  have hp4 : algebraMap V (FractionRing V) w * d ∈ maximalIdeal V ^ n • Submodule.span V {d} := by
    have := Submodule.mem_map_of_mem (f := P.subtype) hp3
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl (Submodule.map_comap_le _ _) this
  obtain ⟨u, hu, hud⟩ := Submodule.mem_smul_span_singleton.1 hp4
  rw [hsm] at hud
  have hwu : w = u := IsFractionRing.injective V (FractionRing V) (mul_right_cancel₀ hd hud).symm
  rw [hwu]
  simpa using Submodule.smul_mem_smul hu (Submodule.mem_top : (1 : V) ∈ (⊤ : Submodule V V))

end GlobalTheory.Poinc.TwistSum₂
