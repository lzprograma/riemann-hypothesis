module

public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalRingCardinality.DataKap
public import Mathlib.NumberTheory.PrimesCongruentOne

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace Formalism.MainNotions.AbsolutelyIrreducibleSpan

open Formalism.BasicNotions

theorem sharp_downTo (D : D7) (μ : D.what₂.Tup) :
    ∀ j, (RowSide.sharp D).downTo μ j = D.what₂.downTo μ j
  | 0 => rfl
  | j + 1 => by
    show ((RowSide.sharp D).downTo μ j).comp (D.what₂.io μ j) = (D.what₂.downTo μ j).comp (D.what₂.io μ j)
    rw [sharp_downTo D μ j]; rfl

theorem sharp_iota (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
  first
  | (unfold RowSide.iota Rows.Data.iota; rw [sharp_downTo D μ D.R.m]; try rfl; done)

theorem sharp_Usp (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).Usp μ = D.what₂.Usp μ := by
  first
  | (unfold RowSide.Usp Rows.Data.Usp; rw [sharp_iota]; try rfl; done)

theorem sharp_Qsp (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).Qsp μ = D.what₂.Qsp μ := by
  first
  | (unfold RowSide.Qsp Rows.Data.Qsp; rw [sharp_Usp]; try rfl; done)

theorem sharp_LamSet (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).LamSet μ = D.what₂.LamSet μ := by
  first
  | (unfold RowSide.LamSet Rows.Data.LamSet; rw [sharp_Qsp]; try rfl; done)
  | (simp only [RowSide.LamSet, Rows.Data.LamSet, sharp_Qsp]; try rfl; done)

theorem sharp_RRset (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).RRset μ = D.what₂.RRset μ := by
  first
  | (unfold RowSide.RRset Rows.Data.RRset; rw [sharp_iota, sharp_LamSet]; try rfl; done)

theorem sharp_RRDef (D : D7) : (RowSide.sharp D).RRDef ↔ DV.RRDef D := by
  first
  | (unfold RowSide.RRDef DV.RRDef; simp only [sharp_RRset]; try exact Iff.rfl; done)

section Derived

variable (D : D7)

def rPr : ℕ :=
  sInf {p : ℕ | p.Prime ∧
    ¬ p ∣ LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK}

def q0 : ℕ := sInf {p : ℕ | p.Prime ∧ p % (rPr D * LevelStarExponents.condE D) = 1 ∧ ¬ p ∣ Ideal.absNorm D.host.ccK}

theorem condE_pos : 0 < LevelStarExponents.condE D := by
  unfold LevelStarExponents.condE
  exact Nat.mul_pos (Nat.mul_pos D.host.QS_pos (lt_of_le_of_lt (Nat.zero_le _) D.host.qd_big.1))
    (lt_of_le_of_lt (Nat.zero_le _) D.host.qd_big.2)

theorem absNorm_ccK_pos : 0 < Ideal.absNorm D.host.ccK := by
  first
  | exact Nat.pos_of_ne_zero (fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.mp h))

theorem rPr_mem : (rPr D).Prime ∧
    ¬ rPr D ∣ LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK := by
  have hN : 0 < LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK := by
    have h1 := D.host.pde_prime.two_le
    have h2 := D.host.pde'_prime.two_le
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (condE_pos D) (by omega)) (by omega)) (absNorm_ccK_pos D)
  obtain ⟨p, hp1, hp2⟩ :=
    Nat.exists_infinite_primes (LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK + 1)
  have hne : {p : ℕ | p.Prime ∧
      ¬ p ∣ LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK}.Nonempty :=
    ⟨p, hp2, fun hd => absurd (Nat.le_of_dvd hN hd) (Nat.not_le.mpr (Nat.lt_of_succ_le hp1))⟩
  exact Nat.sInf_mem hne

theorem auxiliary_prime_mem : (q0 D).Prime ∧ q0 D % (rPr D * LevelStarExponents.condE D) = 1 ∧ ¬ q0 D ∣ Ideal.absNorm D.host.ccK := by
  have hr := (rPr_mem D).1
  have hc := condE_pos D
  have hk : 1 < rPr D * LevelStarExponents.condE D :=
    lt_of_lt_of_le hr.one_lt (le_mul_of_one_le_right (Nat.zero_le _) hc)
  obtain ⟨p, hp, hlt, hmod⟩ :=
    Nat.exists_prime_gt_modEq_one (Ideal.absNorm D.host.ccK) (Nat.pos_iff_ne_zero.mp (lt_trans Nat.zero_lt_one hk))
  have hne : {p : ℕ | p.Prime ∧ p % (rPr D * LevelStarExponents.condE D) = 1 ∧ ¬ p ∣ Ideal.absNorm D.host.ccK}.Nonempty :=
    ⟨p, hp, (show p % _ = 1 % _ from hmod).trans (Nat.mod_eq_of_lt hk),
      fun hd => absurd (Nat.le_of_dvd (absNorm_ccK_pos D) hd) (Nat.not_le.mpr hlt)⟩
  exact Nat.sInf_mem hne

end Derived

theorem auxiliary_prime_odd (D : D7) : q0 D % 2 = 1 := by
  have h2 : 2 ∣ D.host.QS := by
    have ht := D.host.tower_dvd
    exact dvd_trans (dvd_pow_self 2 (by omega)) ht
  have h2c : 2 ∣ LevelStarExponents.condE D := by
    unfold LevelStarExponents.condE
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h2 _) _
  have h2k : 2 ∣ rPr D * LevelStarExponents.condE D := dvd_mul_of_dvd_right h2c _
  rw [← Nat.mod_mod_of_dvd (q0 D) h2k, (auxiliary_prime_mem D).2.1]

end Formalism.MainNotions.AbsolutelyIrreducibleSpan
