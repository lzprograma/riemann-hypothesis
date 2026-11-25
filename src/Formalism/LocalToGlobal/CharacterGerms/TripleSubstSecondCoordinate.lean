module

import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
public import Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffTripleSubstitution
import Formalism.LocalToGlobal.CharacterGerms.SubstSubst
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}

theorem exp_add {σ : Type} {f g : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : mvExp (f + g) = mvExp f * mvExp g := by
  apply GlobalTheory.RowVal.mvExp_add <;> assumption

private theorem hasSubst_of_Z0 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.HasSubst a := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha

theorem exp_nsmul {σ : Type} {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) (k : ℕ) :
    mvExp ((k : C) • f) = mvExp f ^ k := by
  induction k with
  | zero =>
    rw [Nat.cast_zero, zero_smul, pow_zero]
    exact GlobalTheory.RowVal.mvExp_zero'
  | succ k ih =>
    have hk : MvPowerSeries.constantCoeff ((k : C) • f) = 0 := by simp [hf]
    rw [Nat.cast_succ, add_smul, one_smul, exp_add hk hf, ih, pow_succ]

variable (Y : FBChart C V O dd)

section Subst

variable [Finite τ] {A : τ → MvPowerSeries τ' C} (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0)
  {u v : Fin dd → MvPowerSeries τ C} (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0)
  (hv : ∀ i, MvPowerSeries.constantCoeff (v i) = 0)

include hA hu hv in
theorem subst_pair_substitution_comm (f : PS C 2 dd) :
    MvPowerSeries.subst A (MvPowerSeries.subst (P2 u v) f) =
      MvPowerSeries.subst (P2 (fun i => MvPowerSeries.subst A (u i)) (fun i => MvPowerSeries.subst A (v i))) f := by
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_of_Z0 (_root_.Formalism.L2.FormalSeriesBounds.VP.constantCoeff_pair_substitution hu hv)) (hasSubst_of_Z0 hA)]
  congr 1
  funext q
  simp only [P2]
  split_ifs <;> rfl

include hA hu hv in
theorem hAt_subst : MvPowerSeries.subst A (hAt Y u v) =
    hAt Y (fun i => MvPowerSeries.subst A (u i)) (fun i => MvPowerSeries.subst A (v i)) :=  subst_pair_substitution_comm hA hu hv Y.h

include hA hu hv in
theorem addAt_subst (i : Fin dd) : MvPowerSeries.subst A (addAt Y u v i) =
    addAt Y (fun i => MvPowerSeries.subst A (u i)) (fun i => MvPowerSeries.subst A (v i)) i :=  subst_pair_substitution_comm hA hu hv (Y.B.G.F i)

include hA hu in
theorem actAt_subst (x : O) (i : Fin dd) : MvPowerSeries.subst A (actAt Y x u i) =
    actAt Y x (fun i => MvPowerSeries.subst A (u i)) i := by
  show MvPowerSeries.subst A (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => u q.2) (Y.B.A.act x i)) =
    MvPowerSeries.subst (fun q : Fin 1 × Fin dd => MvPowerSeries.subst A (u q.2)) (Y.B.A.act x i)
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_of_Z0 (a := fun q : Fin 1 × Fin dd => u q.2) fun q => hu q.2) (hasSubst_of_Z0 hA)]

end Subst

theorem cc_addAt {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (i : Fin dd) :
    MvPowerSeries.constantCoeff (addAt Y a b i) = 0 :=  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_of_Z0 (_root_.Formalism.L2.FormalSeriesBounds.VP.constantCoeff_pair_substitution ha hb))
    (_root_.Formalism.L2.FormalSeriesBounds.VP.constantCoeff_pair_substitution ha hb) (Y.B.G.const i)

private theorem ev_pt_pair {n : ℕ} (x y : Pt C n dd) : ev (n := n) ![x, y] Y.h = hAt Y x y := by
  show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst (P2 x y) Y.h
  congr 1
  funext q
  rcases q with ⟨j, l⟩
  fin_cases j <;> first | rfl

theorem addOf_eq {n : ℕ} (a b : Pt C n dd) : addOf (Y.B.FK C) a b = addAt Y a b := by
  funext i
  show MvPowerSeries.subst (fun p : Fin 2 × Fin dd => (![a, b] : Fin 2 → Pt C n dd) p.1 p.2)
      (MvPowerSeries.map (algebraMap C C) (Y.B.G.F i)) = MvPowerSeries.subst (P2 a b) (Y.B.G.F i)
  have hm : MvPowerSeries.map (algebraMap C C) (Y.B.G.F i) = Y.B.G.F i := by
    ext n
    simp
  rw [hm]
  congr 1
  funext q
  rcases q with ⟨j, l⟩
  fin_cases j <;> first | rfl

section Three

variable {a b c : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
  (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0)

include ha hb hc

theorem triple_subst_first_coordinate : (fun i => MvPowerSeries.subst (P3 a b c) (pt C dd (0 : Fin 3) i)) = a := by
  funext i
  show MvPowerSeries.subst (P3 a b c) (MvPowerSeries.X ((0 : Fin 3), i)) = a i
  rw [MvPowerSeries.subst_X (hasSubst_of_Z0 (_root_.Formalism.L2.FormalSeriesBounds.VP.constantCoeff_triple_substitution ha hb hc))]
  simp [P3]

theorem triple_subst_second_coordinate : (fun i => MvPowerSeries.subst (P3 a b c) (pt C dd (1 : Fin 3) i)) = b := by
  funext i
  show MvPowerSeries.subst (P3 a b c) (MvPowerSeries.X ((1 : Fin 3), i)) = b i
  rw [MvPowerSeries.subst_X (hasSubst_of_Z0 (_root_.Formalism.L2.FormalSeriesBounds.VP.constantCoeff_triple_substitution ha hb hc))]
  simp [P3]

theorem triple_subst_third_coordinate : (fun i => MvPowerSeries.subst (P3 a b c) (pt C dd (2 : Fin 3) i)) = c := by
  funext i
  show MvPowerSeries.subst (P3 a b c) (MvPowerSeries.X ((2 : Fin 3), i)) = c i
  rw [MvPowerSeries.subst_X (hasSubst_of_Z0 (_root_.Formalism.L2.FormalSeriesBounds.VP.constantCoeff_triple_substitution ha hb hc))]
  simp [P3]

theorem second_partial_law_at_points : MvPowerSeries.subst (P3 a b c) Y.B.ph2 =
    mvExp (hAt Y a b + hAt Y a c - hAt Y a (addAt Y b c)) := by
  have hp : ∀ (j : Fin 3) (i : Fin dd), MvPowerSeries.constantCoeff (pt C dd j i : PS C 3 dd) = 0 :=
    fun j i => MvPowerSeries.constantCoeff_X _
  have hP3 := _root_.Formalism.L2.FormalSeriesBounds.VP.constantCoeff_triple_substitution ha hb hc
  have hg := Y.gauge.ph2
  rw [toK_eq, ev_pt_pair Y, ev_pt_pair Y, ev_pt_pair Y, addOf_eq] at hg
  have hcc : MvPowerSeries.constantCoeff (hAt Y (pt C dd 0) (pt C dd 1) + hAt Y (pt C dd 0) (pt C dd 2) -
      hAt Y (pt C dd (0 : Fin 3)) (addAt Y (pt C dd 1) (pt C dd 2))) = 0 := by
    rw [map_sub, map_add (f := _), cc_hAt Y (hp 0) (hp 1), cc_hAt Y (hp 0) (hp 2),
      cc_hAt Y (hp 0) (cc_addAt Y (hp 1) (hp 2))]
    simp
  rw [hg, expS_eq _ hcc, subst_exp hP3 hcc]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_of_Z0 hP3), map_sub, map_add (f := _), MvPowerSeries.coe_substAlgHom]
  rw [hAt_subst Y hP3 (hp 0) (hp 1), hAt_subst Y hP3 (hp 0) (hp 2),
    hAt_subst Y hP3 (hp 0) (cc_addAt Y (hp 1) (hp 2))]
  have haddS : (fun i => MvPowerSeries.subst (P3 a b c) (addAt Y (pt C dd (1 : Fin 3)) (pt C dd 2) i)) =
      addAt Y b c := by
    funext i
    rw [addAt_subst Y hP3 (hp 1) (hp 2) i, triple_subst_second_coordinate ha hb hc, triple_subst_third_coordinate ha hb hc]
  rw [haddS, triple_subst_first_coordinate ha hb hc, triple_subst_second_coordinate ha hb hc, triple_subst_third_coordinate ha hb hc]

end Three

end VP

end Formalism.L2.FormalSeriesBounds
