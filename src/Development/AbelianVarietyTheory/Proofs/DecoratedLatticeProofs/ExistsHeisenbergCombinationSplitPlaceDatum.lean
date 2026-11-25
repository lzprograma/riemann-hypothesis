module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantOfTsupport
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

namespace GlobalTheory.LocComb

variable {D : D7}

theorem comb_add (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (c + c') f = comb ψ S T c f + comb ψ S T c' f :=
  Finsupp.sum_add_index' (h := fun u (a : ℂ) => a • heisO ψ S T u f) (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

theorem comb_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : ℂ) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (a • c) f = a • comb ψ S T c f := by
  rw [GlobalTheory.HeisComb.comb_eq_sum, GlobalTheory.HeisComb.comb_eq_sum,
    Finsupp.sum_smul_index' (h := fun u (a : ℂ) => a • heisO ψ S T u f) fun _ => zero_smul _ _, Finsupp.smul_sum]
  simp only [smul_eq_mul, mul_smul]

theorem comb_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (y : WO S T) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single y 1) f = heisO ψ S T y f := by
  rw [GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum_single_index (h := fun u (a : ℂ) => a • heisO ψ S T u f) (zero_smul _ _),
    one_smul]

theorem heis_comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {e : AE D} {y : WO S T} (hy : IsHalf e y) {c : WO S T →₀ ℂ}
    (hc : ∀ w ∈ c.support, IsHalf e w) :
    ∃ c' : WO S T →₀ ℂ, (∀ w ∈ c'.support, IsHalf e w) ∧ ∀ f, comb ψ S T c' f = heisO ψ S T y (comb ψ S T c f) := by
  obtain ⟨c', h1, h2⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 (Finsupp.single y 1) c
  refine ⟨c', fun w hw => ?_, fun f => by rw [h2, comb_single]⟩
  obtain ⟨x, hx, z, hz, rfl⟩ := h1 w hw
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx), add_comm]
  exact (Witness.half_add hy).2 (hc z hz)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']


omit [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] in
theorem trans_mem_SB {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (x : Matrix Y Y' k) :
    (fun t => Φ (t + x)) ∈ SB (Matrix Y Y' k) :=
  ⟨hΦ.1.comp_continuous (continuous_add_const x), hΦ.2.comp_homeomorph (Homeomorph.addRight x)⟩


omit [DecidableEq Y] [DecidableEq Y'] in
theorem modul_mem_SB {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {Φ : Matrix Y Y' k → ℂ}
    (hΦ : Φ ∈ SB (Matrix Y Y' k)) (b : Matrix Y Y' k) : (fun t => Inhab.pairing ψ t b * Φ t) ∈ SB (Matrix Y Y' k) := by
  have hψ : IsLocallyConstant ψ := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    filter_upwards [((isOpen_cball d).preimage (continuous_sub_right x)).mem_nhds
      (show x - x ∈ cball d by simp [cball])] with z hz
    rw [← add_sub_cancel x z, AddChar.map_add_eq_mul, (hd d).2 le_rfl _ hz, mul_one]
  have h2 : IsLocallyConstant fun t : Matrix Y Y' k => Inhab.pairing ψ t b :=
    (hψ.comp_continuous (f := fun t : Matrix Y Y' k => ∑ r, ∑ q, b r q * t r q) (by fun_prop)).comp fun z : Circle => (z : ℂ)
  exact ⟨h2.mul hΦ.1, hΦ.2.mul_left⟩

theorem exists_comb : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ Φ₀ Φ : SB (Matrix Y Y' k), Φ₀ ≠ 0 → ∃ c : WO S T →₀ ℂ, (∀ w ∈ c.support, IsHalf (p.e + cA D p.e) w) ∧ ∀ Tm, p.IsModel ψ FS FT Tm → Tm Φ = comb ψ S T c (Tm Φ₀) := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ Φ₀ Φ hΦ₀
  classical
  obtain ⟨⟨ψk, hψk⟩, hcn, -, -, -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨hcont, hne⟩ := hcn ψk hψk
  obtain ⟨d, hd⟩ := exists_hasConductor_of_continuous ψk hcont hne
  obtain ⟨hup, -, -, hsymk, hsurj⟩ := GlobalTheory.LocSympl.halves_at_split D k p Y Y' S T FS FT ψ ψk hψk
  obtain ⟨-, hec, -⟩ := p.split
  have hce : cA D p.e * p.e = 0 := by rw [mul_comm, hec]
  have half1 : ∀ u : WO S T, IsHalf p.e u → IsHalf (p.e + cA D p.e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hce, zero_mul, add_zero, hu i j]
  have half2 : ∀ u : WO S T, IsHalf (cA D p.e) u → IsHalf (p.e + cA D p.e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hec, zero_mul, zero_add, hu i j]
  let M : Submodule ℂ (SB (Matrix Y Y' k)) :=
    { carrier := {Ψ | ∃ c : WO S T →₀ ℂ, (∀ w ∈ c.support, IsHalf (p.e + cA D p.e) w) ∧
        ∀ Tm, p.IsModel ψ FS FT Tm → Tm Ψ = comb ψ S T c (Tm Φ₀)}
      zero_mem' := ⟨0, by simp, fun Tm _ => by simp [comb]⟩
      add_mem' := by
        rintro a b ⟨c, h1, h2⟩ ⟨c', h1', h2'⟩
        refine ⟨c + c', fun w hw => ?_, fun Tm h => by rw [map_add (f := _), comb_add, h2 Tm h, h2' Tm h]⟩
        exact (Finset.mem_union.1 (Finsupp.support_add hw)).elim (h1 w) (h1' w)
      smul_mem' := by
        rintro a b ⟨c, h1, h2⟩
        exact ⟨a • c, fun w hw => h1 w (Finsupp.support_smul hw), fun Tm h => by rw [map_smul, comb_smul, h2 Tm h]⟩ }
  have key : SB (Matrix Y Y' k) ≤ M.map (SB (Matrix Y Y' k)).subtype := by
    refine Inhab.sb_le hd ?_ ?_ Φ₀.2 (fun h => hΦ₀ (Subtype.ext h)) ⟨Φ₀, ⟨Finsupp.single 0 1, fun w hw => ?_, fun Tm _ => ?_⟩, rfl⟩
    · rintro x _ ⟨Ψ, ⟨c, h1, h2⟩, rfl⟩
      obtain ⟨c', h3, h4⟩ := heis_comb ψ S T (half1 _ (hup x).1) h1
      exact ⟨⟨_, trans_mem_SB Ψ.2 x⟩, ⟨c', h3, fun Tm h => by rw [h4, ← h2 Tm h]; exact h.trans x Ψ _ fun _ => rfl⟩, rfl⟩
    · rintro b _ ⟨Ψ, ⟨c, h1, h2⟩, rfl⟩
      obtain ⟨y, hy, hyb⟩ := hsurj b
      obtain ⟨c', h3, h4⟩ := heis_comb ψ S T (half2 _ hy) h1
      refine ⟨⟨_, modul_mem_SB hd Ψ.2 b⟩, ⟨c', h3, fun Tm h => ?_⟩, rfl⟩
      rw [h4, ← h2 Tm h]
      refine h.modul y hy Ψ _ fun t => ?_
      rw [hsymk t y hy, hyb t]
      rfl
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hw)]
      exact fun i j => mul_zero _
    · rw [comb_single]
      funext w
      show _ = ψ (symplOH S T w 0) * Tm Φ₀ (w + 0)
      rw [symplOH, GlobalTheory.PlaceModel.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero]
  obtain ⟨Ψ, hΨ, e⟩ := key Φ.2
  rw [← show Ψ = Φ from Subtype.ext e]
  exact hΨ

end GlobalTheory.LocComb

end
