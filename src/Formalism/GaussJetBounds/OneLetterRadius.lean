module

public import Formalism.GaussJetBounds.GenLogInverse
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HomWProd
public import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison
public import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Data.Nat.Prime.Factorial
public import Formalism.GaussJetBounds.Statement
public import Formalism.GaussJetBounds.GaussJetProofs.AsmOne
public import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffEvenDerivativeEqZero
public import Formalism.GaussJetBounds.GaussJetProofs.OneLetterRadiusIdentity
import Mathlib.Tactic.Linter.HaveILetI
import Formalism.FormalGroupLog.Statement
import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.GaussJetBounds.GaussJetProofs.ExistsNeZeroOfFinsumNeZero, Formalism.TorsionNormIteration.InverseIntegralClasses.NormNatCastOfNotDvd, Formalism.GaussJetBounds.GaussJetProofs.LogStep, Formalism.GaussJetBounds.GaussJetProofs.SwappedParitySeriesBinomialForm, Formalism.GaussJetBounds.OneLetterRadius

-- ===== clump member: Formalism.GaussJetBounds.GaussJetProofs.ExistsNeZeroOfFinsumNeZero =====
-- clump-header: {"m": "Formalism.GaussJetBounds.GaussJetProofs.ExistsNeZeroOfFinsumNeZero", "h": "module\n\npublic import Formalism.GaussJetBounds.GenLogInverse\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HomWProd\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights

namespace ExponentialDerivativeInverse

section Sub

variable {K : Type u} [NormedField K] {ι : Type v} {K0 : Subfield K}

def InSub (K0 : Subfield K) (f : MvPowerSeries ι K) : Prop :=
  ∀ n, MvPowerSeries.coeff n f ∈ K0

theorem inSub_add {f g : MvPowerSeries ι K} (hf : InSub K0 f) (hg : InSub K0 g) :
    InSub K0 (f + g) := fun n => by rw [map_add (f := _)]; exact K0.add_mem (hf n) (hg n)

theorem inSub_sub {f g : MvPowerSeries ι K} (hf : InSub K0 f) (hg : InSub K0 g) :
    InSub K0 (f - g) := fun n => by rw [map_sub]; exact K0.sub_mem (hf n) (hg n)

theorem inSub_zero : InSub K0 (0 : MvPowerSeries ι K) := fun n => by
  rw [map_zero]; exact K0.zero_mem

theorem inSub_one : InSub K0 (1 : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact K0.one_mem
  · exact K0.zero_mem

theorem inSub_X (x : ι) : InSub K0 (MvPowerSeries.X x : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact K0.one_mem
  · exact K0.zero_mem

theorem inSub_mul {f g : MvPowerSeries ι K} (hf : InSub K0 f) (hg : InSub K0 g) :
    InSub K0 (f * g) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact K0.sum_mem fun p _ => K0.mul_mem (hf p.1) (hg p.2)

theorem inSub_pow {f : MvPowerSeries ι K} (hf : InSub K0 f) (k : ℕ) : InSub K0 (f ^ k) := by
  induction k with
  | zero => simpa using (inSub_one : InSub K0 (1 : MvPowerSeries ι K))
  | succ k ih => rw [pow_succ]; exact inSub_mul ih hf

theorem inSub_prod {α : Type w} (s : Finset α) (F : α → MvPowerSeries ι K)
    (h : ∀ i ∈ s, InSub K0 (F i)) : InSub K0 (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (inSub_one : InSub K0 (1 : MvPowerSeries ι K))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact inSub_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem finsum_mem_sub {α : Type w} (g : α → K) (h : ∀ i, g i ∈ K0) : ∑ᶠ i, g i ∈ K0 := by
  classical
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum g hfin]
    exact K0.sum_mem fun i _ => h i
  · rw [finsum_of_infinite_support hfin]
    exact K0.zero_mem

theorem inSub_subst {σ : Type w} [Finite σ] {a : σ → MvPowerSeries ι K}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, InSub K0 (a s))
    {f : MvPowerSeries σ K} (hf : InSub K0 f) : InSub K0 (MvPowerSeries.subst a f) := by
  intro n
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0)]
  refine finsum_mem_sub _ fun m => ?_
  rw [smul_eq_mul]
  exact K0.mul_mem (hf m) (inSub_prod m.support _ (fun s _ => inSub_pow (ha s) _) n)

theorem inSub_mvExp [CharZero K] {D : MvPowerSeries ι K}
    (hD0 : MvPowerSeries.constantCoeff D = 0) (hD : InSub K0 D) : InSub K0 (mvExp D) := by
  intro n
  unfold mvExp
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hD0)]
  refine finsum_mem_sub _ fun k => ?_
  rw [smul_eq_mul, PowerSeries.coeff_exp]
  have hq : algebraMap ℚ K (1 / (k.factorial : ℚ)) ∈ K0 := by
    rw [map_div₀, map_one, map_natCast]
    exact K0.div_mem K0.one_mem (natCast_mem K0 _)
  exact K0.mul_mem hq (inSub_pow hD k n)

end Sub

section Wt

variable {K : Type u} [NormedField K] {ι : Type v}

def wsum (w : ι → ℤ) (n : ι →₀ ℕ) : ℤ := n.sum fun x k => (k : ℤ) * w x

theorem wsum_add (w : ι → ℤ) (m n : ι →₀ ℕ) : wsum w (m + n) = wsum w m + wsum w n := by
  classical
  unfold wsum
  exact Finsupp.sum_add_index' (fun i => by simp) (fun i a b => by push_cast; ring)

theorem wsum_zero (w : ι → ℤ) : wsum w (0 : ι →₀ ℕ) = 0 := by simp [wsum]

theorem wsum_single (w : ι → ℤ) (x : ι) (k : ℕ) : wsum w (Finsupp.single x k) = k * w x := by
  simp [wsum]

def HomW (w : ι → ℤ) (c : ℤ) (f : MvPowerSeries ι K) : Prop :=
  ∀ n, MvPowerSeries.coeff n f ≠ 0 → wsum w n = c

def CongW (N : ℤ) (w : ι → ℤ) (f : MvPowerSeries ι K) : Prop :=
  ∀ n, MvPowerSeries.coeff n f ≠ 0 → N ∣ wsum w n

theorem exists_ne_zero_of_finsum_ne_zero {α : Type w} {g : α → K} (h : ∑ᶠ i, g i ≠ 0) :
    ∃ i, g i ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (finsum_eq_zero_of_forall_eq_zero hc)

variable {w : ι → ℤ}

theorem homW_X (x : ι) : HomW w (w x) (MvPowerSeries.X x : MvPowerSeries ι K) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_X] at hn
  split_ifs at hn with h
  · rw [h, wsum_single]; simp
  · exact absurd rfl hn

theorem homW_zero (c : ℤ) : HomW w c (0 : MvPowerSeries ι K) := by
  intro n hn; simp at hn

theorem homW_one : HomW w 0 (1 : MvPowerSeries ι K) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_one] at hn
  split_ifs at hn with h
  · rw [h, wsum_zero]
  · exact absurd rfl hn

theorem homW_add {c : ℤ} {f g : MvPowerSeries ι K} (hf : HomW w c f) (hg : HomW w c g) :
    HomW w c (f + g) := by
  intro n hn
  rw [map_add (f := _)] at hn
  by_cases h : MvPowerSeries.coeff n f = 0
  · rw [h, zero_add] at hn; exact hg n hn
  · exact hf n h

theorem homW_mul {c c' : ℤ} {f g : MvPowerSeries ι K} (hf : HomW w c f) (hg : HomW w c' g) :
    HomW w (c + c') (f * g) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_mul] at hn
  obtain ⟨p, hp, hpn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, wsum_add, hf p.1 (left_ne_zero_of_mul hpn), hg p.2 (right_ne_zero_of_mul hpn)]

theorem homW_pow {c : ℤ} {f : MvPowerSeries ι K} (hf : HomW w c f) (k : ℕ) :
    HomW w (k * c) (f ^ k) := by
  induction k with
  | zero => intro n hn; simpa using homW_one n (by simpa using hn)
  | succ k ih =>
    rw [pow_succ]
    intro n hn
    rw [homW_mul ih hf n hn]
    push_cast; ring

theorem homW_prod {α : Type w} (s : Finset α) (c : α → ℤ) (F : α → MvPowerSeries ι K)
    (h : ∀ i ∈ s, HomW w (c i) (F i)) : HomW w (∑ i ∈ s, c i) (∏ i ∈ s, F i) := by
  first | (apply UpperTheory.Reformulated.B.Qi22.homW_prod <;> assumption)

variable {N : ℤ}

theorem congW_sub {f g : MvPowerSeries ι K} (hf : CongW N w f) (hg : CongW N w g) :
    CongW N w (f - g) := by
  intro n hn
  rw [map_sub] at hn
  by_cases h : MvPowerSeries.coeff n f = 0
  · rw [h, zero_sub, neg_ne_zero] at hn; exact hg n hn
  · exact hf n h

theorem congW_one : CongW N w (1 : MvPowerSeries ι K) := by
  intro n hn
  rw [homW_one n hn]
  exact dvd_zero N

theorem congW_mul {f g : MvPowerSeries ι K} (hf : CongW N w f) (hg : CongW N w g) :
    CongW N w (f * g) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_mul] at hn
  obtain ⟨p, hp, hpn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, wsum_add]
  exact dvd_add (hf p.1 (left_ne_zero_of_mul hpn)) (hg p.2 (right_ne_zero_of_mul hpn))

theorem congW_pow {f : MvPowerSeries ι K} (hf : CongW N w f) (k : ℕ) : CongW N w (f ^ k) := by
  induction k with
  | zero => simpa using (congW_one : CongW N w (1 : MvPowerSeries ι K))
  | succ k ih => rw [pow_succ]; exact congW_mul ih hf

theorem congW_subst {σ : Type w} [Finite σ] {w1 : σ → ℤ} {a : σ → MvPowerSeries ι K}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, HomW w (w1 s) (a s))
    {f : MvPowerSeries σ K} (hf : CongW N w1 f) : CongW N w (MvPowerSeries.subst a f) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0)] at hn
  obtain ⟨m, hm⟩ := exists_ne_zero_of_finsum_ne_zero hn
  simp only [smul_eq_mul] at hm
  have h1 := hf m (left_ne_zero_of_mul hm)
  have h2 := homW_prod m.support (fun s => (m s : ℤ) * w1 s) (fun s => a s ^ m s)
    (fun s _ => homW_pow (ha s) (m s)) n (right_ne_zero_of_mul hm)
  rw [h2]
  exact h1

theorem congW_mvExp [CharZero K] {D : MvPowerSeries ι K}
    (hD0 : MvPowerSeries.constantCoeff D = 0) (hD : CongW N w D) : CongW N w (mvExp D) := by
  intro n hn
  unfold mvExp at hn
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hD0)] at hn
  obtain ⟨k, hk⟩ := exists_ne_zero_of_finsum_ne_zero hn
  simp only [smul_eq_mul] at hk
  exact congW_pow hD k n (right_ne_zero_of_mul hk)

theorem zpow_sum_of_ne {α : Type w} (s : Finset α) {ζ : K} (hζ : ζ ≠ 0) (f : α → ℤ) :
    ζ ^ (∑ i ∈ s, f i) = ∏ i ∈ s, ζ ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hζ, ih]

end Wt

section Torus

variable {K : Type u} [NormedField K] {d : ℕ}

theorem congW_of_torus {l : ℕ} [NeZero d] {ζ : K} (hN : l ^ d - 1 ≠ 0)
    (hζ : IsPrimitiveRoot ζ (l ^ d - 1)) {be : MvPowerSeries (ZMod d) K}
    (hbe : MvPowerSeries.subst (torus l ζ) be = be) :
    CongW ((l ^ d - 1 : ℕ) : ℤ) (lw l) be := by
  classical
  intro n hn
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN
  have ht : torus (d := d) l ζ = (fun s : ZMod d => ζ ^ lw l s) • (MvPowerSeries.X : ZMod d → MvPowerSeries (ZMod d) K) := by
    funext s
    simp [torus, MvPowerSeries.smul_eq_C_mul]
  rw [ht, ← MvPowerSeries.rescale_eq_subst] at hbe
  have hc := congrArg (MvPowerSeries.coeff n) hbe
  rw [MvPowerSeries.coeff_rescale] at hc
  have hprod : (n.prod fun s m => (ζ ^ lw l s) ^ m) = ζ ^ wsum (lw l) n := by
    unfold wsum Finsupp.prod Finsupp.sum
    rw [zpow_sum_of_ne _ hζ0]
    refine Finset.prod_congr rfl fun s _ => ?_
    beta_reduce
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [hprod] at hc
  have hu : ζ ^ wsum (lw l) n = 1 := by
    have h2 : (ζ ^ wsum (lw l) n - 1) * MvPowerSeries.coeff n be = 0 := by
      rw [sub_mul, hc, one_mul, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hn
  exact (hζ.zpow_eq_one_iff_dvd _).mp hu

end Torus

section Diff

variable {K : Type u} [NormedField K] {d : ℕ}

def Good (K0 : Subfield K) (N : ℤ) (w : V2 d → ℤ) (f : MvPowerSeries (V2 d) K) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ InSub K0 f ∧ CongW N w f

theorem good_sub {K0 : Subfield K} {N : ℤ} {w : V2 d → ℤ} {f g : MvPowerSeries (V2 d) K}
    (hf : Good K0 N w f) (hg : Good K0 N w g) : Good K0 N w (f - g) :=
  ⟨by rw [map_sub, hf.1, hg.1, sub_zero], inSub_sub hf.2.1 hg.2.1, congW_sub hf.2.2 hg.2.2⟩

def Fam (K0 : Subfield K) (l : ℕ) (a : ZMod d → MvPowerSeries (V2 d) K) : Prop :=
  ∀ s, MvPowerSeries.constantCoeff (a s) = 0 ∧ InSub K0 (a s) ∧
    HomW (fun x : V2 d => lw l x.2) (lw l s) (a s)

theorem good_subst [NeZero d] {K0 : Subfield K} {l : ℕ} {N : ℤ} {be : MvPowerSeries (ZMod d) K}
    (hK0 : InSub K0 be) (hcc : MvPowerSeries.constantCoeff be = 0) (hcb : CongW N (lw l) be)
    {a : ZMod d → MvPowerSeries (V2 d) K} (ha : Fam K0 l a) :
    Good K0 N (fun x : V2 d => lw l x.2) (MvPowerSeries.subst a be) :=
  ⟨MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => (ha s).1) (fun s => (ha s).1) hcc,
    inSub_subst (fun s => (ha s).1) (fun s => (ha s).2.1) hK0,
    congW_subst (fun s => (ha s).1) (fun s => (ha s).2.2) hcb⟩

variable {K0 : Subfield K} {l : ℕ}

theorem zero_series_family : Fam K0 l (s0 (K := K) (d := d)) := fun s =>
  ⟨by simp [s0], inSub_X _, homW_X (false, s)⟩

theorem oddIndicator_alt_series_family : Fam K0 l (s1 (K := K) (d := d)) := by
  intro s
  unfold s1
  split_ifs
  · exact ⟨by simp, inSub_add (inSub_X _) (inSub_X _),
      homW_add (homW_X (false, s)) (homW_X (true, s))⟩
  · exact ⟨by simp, inSub_add (inSub_X _) inSub_zero,
      homW_add (homW_X (false, s)) (homW_zero _)⟩

theorem swappedParity_series_family : Fam K0 l (s2 (K := K) (d := d)) := by
  intro s
  unfold s2
  split_ifs
  · exact ⟨by simp, inSub_X _, homW_X (true, s)⟩
  · exact ⟨by simp, inSub_X _, homW_X (false, s)⟩

theorem oddIndicator_series_family : Fam K0 l (s1' (K := K) (d := d)) := by
  intro s
  unfold s1'
  split_ifs
  · exact ⟨by simp, inSub_add (inSub_X _) inSub_zero,
      homW_add (homW_X (false, s)) (homW_zero _)⟩
  · exact ⟨by simp, inSub_add (inSub_X _) (inSub_X _),
      homW_add (homW_X (false, s)) (homW_X (true, s))⟩

theorem parityIndicator_series_family : Fam K0 l (s2' (K := K) (d := d)) := by
  intro s
  unfold s2'
  split_ifs
  · exact ⟨by simp, inSub_X _, homW_X (false, s)⟩
  · exact ⟨by simp, inSub_X _, homW_X (true, s)⟩

end Diff

end ExponentialDerivativeInverse


open ExponentialDerivativeInverse in
theorem exponential_derivative_inverse : ExpDeInv.{u} := open ExponentialDerivativeInverse in by
  intro K _ _ l d _ hl hd _ K0 ζ hζ be hK0 htor hcc D hD
  have hN : l ^ d - 1 ≠ 0 := by
    have h2 : 2 ≤ l ^ d := le_trans hl.two_le (Nat.le_self_pow (by omega) l)
    omega
  have hcb := congW_of_torus hN hζ htor
  have hD' : Good K0 ((l ^ d - 1 : ℕ) : ℤ) (fun x : V2 d => lw l x.2) D := by
    rcases hD with rfl | rfl
    · exact good_sub (good_sub (good_subst hK0 hcc hcb oddIndicator_alt_series_family) (good_subst hK0 hcc hcb zero_series_family))
        (good_subst hK0 hcc hcb swappedParity_series_family)
    · exact good_sub (good_sub (good_subst hK0 hcc hcb oddIndicator_series_family) (good_subst hK0 hcc hcb zero_series_family))
        (good_subst hK0 hcc hcb parityIndicator_series_family)
  exact ⟨inSub_mvExp hD'.1 hD'.2.1, fun n hn => congW_mvExp hD'.1 hD'.2.2 n hn⟩

end Formalism.DworkPowerSeriesWeights
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.GaussJetBounds.GaussJetProofs.ExistsNeZeroOfFinsumNeZero =====

-- ===== clump member: Formalism.TorsionNormIteration.InverseIntegralClasses.NormNatCastOfNotDvd =====
-- clump-header: {"m": "Formalism.TorsionNormIteration.InverseIntegralClasses.NormNatCastOfNotDvd", "h": "module\n\nimport Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat\npublic import Mathlib.Analysis.Normed.Field.Basic\npublic import Mathlib.Data.Nat.PadicValNat\npublic import Mathlib.Data.Nat.Prime.Defs\npublic import Mathlib.Topology.MetricSpace.Ultra.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\npublic import Mathlib.Analysis.Normed.Ring.Ultra\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.FormalGroupLog.Statement\npublic import Mathlib.Analysis.Normed.Group.Ultra\npublic import Mathlib.Data.Nat.Factorization.Basic\npublic import Mathlib.NumberTheory.Padics.PadicVal.Basic\nimport Mathlib.RingTheory.PowerSeries.Basic\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open PowerSeries

universe u

namespace Formalism.LT.ExpP

open Formalism.G

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma norm_natCast_of_not_dvd {p m : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (hm : ¬ p ∣ m) :
    ‖(m : K)‖ = 1 := by
  apply Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd <;> assumption

lemma norm_natCast_eq {p n : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (hn : n ≠ 0) :
    ‖(n : K)‖ = ‖(p : K)‖ ^ padicValNat p n := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  haveI := Fact.mk hp
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (pow_ne_zero _ hp.ne_zero) hm0, _root_.Nat.padicValNat_def, _root_.Nat.multiplicity_prime_pow, _root_.Nat.padicValNat_def,
    _root_.multiplicity_eq_zero_of_not_dvd hm, add_zero]
  push_cast
  rw [norm_mul, norm_pow, norm_natCast_of_not_dvd hp hp1 hm, mul_one]

end Formalism.LT.ExpP
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.TorsionNormIteration.InverseIntegralClasses.NormNatCastOfNotDvd =====

-- ===== clump member: Formalism.GaussJetBounds.GaussJetProofs.LogStep =====
-- clump-header: {"m": "Formalism.GaussJetBounds.GaussJetProofs.LogStep", "h": "module\n\npublic import Formalism.GaussJetBounds.GenLogInverse\npublic import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison\nimport Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound\npublic import Formalism.TorsionNormIteration.InverseIntegralClasses.NormNatCastOfNotDvd\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights

open MvPowerSeries
open Formalism.FG.SolveVAux (Low low_mono low_add low_mul low_pow low_one_iff)

theorem padicValNat_factorial_le_sub_one_div {l : ℕ} (hl : l.Prime) {k : ℕ} (hk : k ≠ 0) :
    (padicValNat l k.factorial : ℝ) ≤ ((k : ℝ) - 1) * (1 / ((l : ℝ) - 1)) := by
  have := Fact.mk hl
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero l hk
  have hl2 := hl.two_le
  have h1 : (l - 1) * padicValNat l k.factorial ≤ k - 1 := by
    rw [Nat.padicValNat_def]
    omega
  have h2 : (((l - 1) * padicValNat l k.factorial : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast h1
  rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ l), Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hk),
    Nat.cast_one] at h2
  have hpos : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl2
    linarith
  rw [mul_one_div, le_div_iff₀ hpos, mul_comm]
  exact h2

theorem norm_coeff_exp {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ}
    (hl : l.Prime) (hπ : ‖(l : K)‖ < 1) (k : ℕ) :
    ‖PowerSeries.coeff k (PowerSeries.exp K)‖ = (‖(l : K)‖ ^ padicValNat l k.factorial)⁻¹ := by
  rw [PowerSeries.coeff_exp, map_div₀, map_one, map_natCast, norm_div, norm_one, one_div,
    Formalism.LT.ExpP.norm_natCast_eq hl hπ (Nat.factorial_ne_zero k)]

theorem logarithm_weight_induction : LogStep.{u, v} := by
  intro K _ _ _ l hl hπ ι r D hD0 hE
  classical
  have hπ0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  have hπ1 : ‖(l : K)‖ ≤ 1 := hπ.le
  have hD1 : Low 1 D := (low_one_iff _).2 hD0
  have hs : PowerSeries.HasSubst D := PowerSeries.HasSubst.of_constantCoeff_zero hD0
  suffices H : ∀ N, ∀ n : ι →₀ ℕ, n.degree = N →
      MonoWtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) n (coeff n D) from fun n => H _ n rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n hn
  by_cases hn0 : n = 0
  · subst hn0
    rw [monoWtGe_iff, coeff_zero_eq_constantCoeff_apply, hD0, norm_zero]
    exact Real.rpow_nonneg hπ0.le _
  have hTw : WtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) (truncBelow N D) := by
    intro m
    rw [monoWtGe_iff, coeff_truncBelow]
    split_ifs with hm
    · exact ih _ hm m rfl
    · simpa using Real.rpow_nonneg hπ0.le _
  have hlow : Low N (D - truncBelow N D) := by
    intro m hm
    rw [map_sub, coeff_truncBelow, ite_eq_left hm, sub_self]
  have hT1 : Low 1 (truncBelow N D) := by
    intro m hm
    rw [coeff_truncBelow]
    split_ifs
    · exact hD1 m hm
    · rfl
  have hpow : ∀ k, Low (N + k) (D ^ (k + 1) - truncBelow N D ^ (k + 1)) := by
    intro k
    induction k with
    | zero => simpa using hlow
    | succ k ihk =>
      have e : D ^ (k + 1 + 1) - truncBelow N D ^ (k + 1 + 1) =
          (D ^ (k + 1) - truncBelow N D ^ (k + 1)) * D +
            truncBelow N D ^ (k + 1) * (D - truncBelow N D) := by ring
      rw [e]
      exact low_add (low_mono (le_of_eq (by omega)) (low_mul ihk hD1))
        (low_mono (le_of_eq (by omega)) (low_mul (low_pow hT1 (k + 1)) hlow))

  set a : ℕ → K := fun k => PowerSeries.coeff k (PowerSeries.exp K) • coeff n (D ^ k) with ha
  have hafin : (Function.support a).Finite := PowerSeries.coeff_subst_finite hs _ n
  set b : ℕ → K := fun k => if k = 1 then 0 else a k with hb
  set c : ℕ → K := fun k => if k = 1 then a 1 else 0 with hc
  have hbfin : (Function.support b).Finite :=
    hafin.subset fun k hk => by
      simp only [Function.mem_support, hb] at hk ⊢
      split_ifs at hk with h
      · exact absurd rfl hk
      · exact hk
  have hcfin : (Function.support c).Finite :=
    (Set.finite_singleton 1).subset fun k hk => by
      simp only [Function.mem_support, hc] at hk
      split_ifs at hk with h
      · exact h
      · exact absurd rfl hk
  have habc : a = fun k => b k + c k := by
    funext k
    simp only [hb, hc]
    split_ifs with h
    · subst h; simp
    · simp
  have ha1 : a 1 = coeff n D := by
    simp [ha, PowerSeries.coeff_exp]
  have hsum : coeff n (mvExp D) = (∑ᶠ k, b k) + coeff n D := by
    unfold mvExp
    rw [PowerSeries.coeff_subst hs]
    change ∑ᶠ k, a k = _
    rw [habc, finsum_add_distrib hbfin hcfin, finsum_eq_single c 1 (fun k hk => ite_eq_right hk)]
    simp only [hc, ite_eq_left rfl, ha1]
  have hEq : coeff n D = coeff n (mvExp D - 1) + -(∑ᶠ k, b k) := by
    rw [map_sub, coeff_one, ite_eq_right hn0, sub_zero, hsum]
    ring
  rw [monoWtGe_iff, hEq]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hE n) ?_)
  rw [norm_neg]
  refine norm_finsum_le_of (Real.rpow_nonneg hπ0.le _) fun k => ?_
  simp only [hb]
  split_ifs with hk1
  · simpa using Real.rpow_nonneg hπ0.le _
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk0 : k = 0 := by omega
    subst hk0
    simp only [ha, pow_zero, coeff_one, ite_eq_right hn0, smul_zero, norm_zero]
    exact Real.rpow_nonneg hπ0.le _

  have hce : coeff n (D ^ k) = coeff n (truncBelow N D ^ k) := by
    have := hpow (k - 1) n (by omega)
    rw [Nat.sub_add_cancel (by omega), map_sub, sub_eq_zero] at this
    exact this
  have hbd := wtGe_pow hπ0 hTw k n
  rw [monoWtGe_iff] at hbd
  have hv := padicValNat_factorial_le_sub_one_div hl (k := k) (by omega)
  simp only [ha]
  rw [smul_eq_mul, norm_mul, norm_coeff_exp hl hπ, hce]
  set v := padicValNat l k.factorial
  calc (‖(l : K)‖ ^ v)⁻¹ * ‖coeff n (truncBelow N D ^ k)‖
      ≤ (‖(l : K)‖ ^ v)⁻¹ * ‖(l : K)‖ ^ ((k : ℝ) * (1 / ((l : ℝ) - 1)) - dot n r) :=
        mul_le_mul_of_nonneg_left hbd (inv_nonneg.2 (pow_nonneg hπ0.le _))
    _ = ‖(l : K)‖ ^ ((k : ℝ) * (1 / ((l : ℝ) - 1)) - dot n r - (v : ℝ)) := by
        rw [Real.rpow_sub hπ0 _ (v : ℝ), Real.rpow_natCast]
        ring
    _ ≤ ‖(l : K)‖ ^ (1 / ((l : ℝ) - 1) - dot n r) := by
        apply Real.rpow_le_rpow_of_exponent_ge hπ0 hπ1
        nlinarith

end Formalism.DworkPowerSeriesWeights
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.GaussJetBounds.GaussJetProofs.LogStep =====

-- ===== clump member: Formalism.GaussJetBounds.GaussJetProofs.SwappedParitySeriesBinomialForm =====
-- clump-header: {"m": "Formalism.GaussJetBounds.GaussJetProofs.SwappedParitySeriesBinomialForm", "h": "module\n\npublic import Formalism.GaussJetBounds.GenLogInverse\npublic import Mathlib.Analysis.Normed.Ring.Ultra\npublic import Mathlib.Data.Nat.Choose.Lucas\npublic import Mathlib.Data.Nat.Prime.Factorial\npublic import Mathlib.Analysis.Normed.Group.Ultra\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open MvPowerSeries Formalism.IncomingBounds

theorem bnx_lin_pow {K : Type u} [Field K] {σ : Type*} [DecidableEq σ] (x y : σ) (a b : K) (k : ℕ) (μ : σ →₀ ℕ) :
    coeff μ ((C a * X x + C b * X y : MvPowerSeries σ K) ^ k) =
      ∑ r ∈ Finset.range (k + 1), if Finsupp.single x r + Finsupp.single y (k - r) = μ then
        a ^ r * b ^ (k - r) * (k.choose r : K) else 0 := by
  rw [add_pow, map_sum]; refine Finset.sum_congr rfl fun r _ => ?_
  rw [show (C a * X x : MvPowerSeries σ K) ^ r * (C b * X y) ^ (k - r) * ((k.choose r : ℕ) : MvPowerSeries σ K) =
      C (a ^ r * b ^ (k - r) * (k.choose r : K)) * (X x ^ r * X y ^ (k - r)) by
    simp only [map_mul, map_pow, map_natCast]; ring,
    coeff_C_mul, X_pow_eq, X_pow_eq, monomial_mul_monomial, one_mul, coeff_monomial]
  by_cases h : Finsupp.single x r + Finsupp.single y (k - r) = μ
  · subst h; simp
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h, mul_zero]

theorem bnx_single_add_single_eq {σ : Type*} {x y : σ} (hxy : x ≠ y) (r s i j : ℕ) :
    Finsupp.single x r + Finsupp.single y s = Finsupp.single x i + Finsupp.single y j ↔ r = i ∧ s = j :=
  ⟨fun h => ⟨by simpa [Finsupp.single_apply, hxy] using DFunLike.congr_fun h x,
    by simpa [Finsupp.single_apply, hxy.symm] using DFunLike.congr_fun h y⟩, by rintro ⟨rfl, rfl⟩; rfl⟩

theorem bnx_lin_pow_val {K : Type u} [Field K] {σ : Type*} [DecidableEq σ] {x y : σ} (hxy : x ≠ y)
    (a b : K) (k i j : ℕ) :
    coeff (Finsupp.single x i + Finsupp.single y j) ((C a * X x + C b * X y : MvPowerSeries σ K) ^ k) =
      if i + j = k then a ^ i * b ^ j * (k.choose i : K) else 0 := by
  rw [bnx_lin_pow]; simp_rw [bnx_single_add_single_eq hxy]; split_ifs with hk
  · rw [Finset.sum_eq_single i]
    · simp [show k - i = j by omega]
    · intro _ _ hr; split_ifs with h <;> [exact absurd h.1 hr; rfl]
    · exact fun hi => absurd (Finset.mem_range.2 (by omega)) hi
  · refine Finset.sum_eq_zero fun r hr => ?_
    split_ifs with h <;> [exact absurd (by have := Finset.mem_range.1 hr; omega) hk; rfl]

theorem bnx_lin_pow_supp {K : Type u} [Field K] {σ : Type*} [DecidableEq σ] (x y : σ) (a b : K) (k : ℕ) (μ : σ →₀ ℕ)
    (h : coeff μ ((C a * X x + C b * X y : MvPowerSeries σ K) ^ k) ≠ 0) (z : σ) (hz : μ z ≠ 0) : z = x ∨ z = y := by
  rw [bnx_lin_pow] at h; obtain ⟨r, _, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at hr with hμ
  · subst hμ; by_contra hne; rw [not_or] at hne; exact hz (by simp [Ne.symm hne.1, Ne.symm hne.2])
  · exact absurd rfl hr

section Blocks
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]

def bnxA (a b : ZMod d → K) (s : ZMod d) : MvPowerSeries (V2 d) K :=
  C (a s) * X (false, s) + C (b s) * X (true, s)

def bnxRes (m : V2 d →₀ ℕ) (s : ZMod d) : V2 d →₀ ℕ :=
  Finsupp.single (false, s) (m (false, s)) + Finsupp.single (true, s) (m (true, s))

theorem bnxRes_apply (m : V2 d →₀ ℕ) (s : ZMod d) (z : V2 d) :
    bnxRes m s z = if z.2 = s then m z else 0 := by
  have _ := NeZero.ne d; obtain ⟨b, t⟩ := z
  by_cases h : t = s
  · subst h; cases b <;> simp [bnxRes]
  · cases b <;> simp [bnxRes, h]

theorem bnx_coeff_prod (a b : ZMod d → K) (k : ZMod d → ℕ) (m : V2 d →₀ ℕ) :
    coeff m (∏ s, bnxA a b s ^ k s) = ∏ s, coeff (bnxRes m s) (bnxA a b s ^ k s) := by
  suffices ∀ (S : Finset (ZMod d)) (m : V2 d →₀ ℕ), coeff m (∏ s ∈ S, bnxA a b s ^ k s) =
      if ∀ z : V2 d, z.2 ∉ S → m z = 0 then ∏ s ∈ S, coeff (bnxRes m s) (bnxA a b s ^ k s) else 0 by
    simpa using this Finset.univ m
  intro S m; induction S using Finset.induction_on generalizing m with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, coeff_one]; by_cases hm : m = 0
    · subst hm; simp
    · rw [ite_eq_right hm, ite_eq_right fun h => hm (Finsupp.ext fun z => h z (by simp))]
  | insert c S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, coeff_mul,
      Finset.sum_eq_single (bnxRes m c, m - bnxRes m c), ih]
    · have hcond : (∀ z : V2 d, z.2 ∉ S → (m - bnxRes m c) z = 0) ↔
          (∀ z : V2 d, z.2 ∉ insert c S → m z = 0) :=
        ⟨fun h z hz => by
          simpa [bnxRes_apply, show z.2 ≠ c from fun e => hz (e ▸ Finset.mem_insert_self c S)]
            using h z fun hS => hz (Finset.mem_insert_of_mem hS),
        fun h z hz => by
          simp only [Finsupp.tsub_apply, bnxRes_apply]
          split_ifs with hzc <;> [omega; simp [h z (by simp [hzc, hz])]]⟩
      by_cases hc : ∀ z : V2 d, z.2 ∉ insert c S → m z = 0
      · rw [ite_eq_left (hcond.2 hc), ite_eq_left hc]
        refine congrArg (_ * ·) (Finset.prod_congr rfl fun s hs => congrArg (coeff · _) ?_)
        ext z; simp only [bnxRes_apply, Finsupp.tsub_apply]
        by_cases hz : z.2 = s <;> [simp [hz, show s ≠ c from fun e => ha (e ▸ hs)]; simp [hz]]
      · rw [ite_eq_right (mt hcond.1 hc), ite_eq_right hc, mul_zero]
    · intro p hp hne; rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_contra hnz; have h1 := left_ne_zero_of_mul hnz; have h2 := right_ne_zero_of_mul hnz; rw [ih] at h2
      have hP : ∀ z : V2 d, z.2 ∉ S → p.2 z = 0 := by split_ifs at h2 with hP <;> [exact hP; exact absurd rfl h2]
      have e1 : p.1 = bnxRes m c := by
        ext z; rw [bnxRes_apply]; split_ifs with hz
        · have h3 := DFunLike.congr_fun hp z; have h4 := hP z (hz ▸ ha); rw [Finsupp.add_apply] at h3; omega
        · by_contra hz0; rcases bnx_lin_pow_supp _ _ _ _ _ _ h1 z hz0 with rfl | rfl <;> exact hz rfl
      refine hne (Prod.ext e1 (Finsupp.ext fun z => ?_))
      have h3 := DFunLike.congr_fun hp z; rw [Finsupp.add_apply] at h3; rw [Finsupp.tsub_apply, ← e1]; omega
    · intro h; refine absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (Finsupp.ext fun z => ?_)) h
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, bnxRes_apply]; split_ifs <;> omega
end Blocks

section Subst
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]

def bnxN (m : V2 d →₀ ℕ) : ZMod d →₀ ℕ := Finsupp.equivFunOnFinite.symm fun s => m (false, s) + m (true, s)

theorem bnxN_apply (m : V2 d →₀ ℕ) (s : ZMod d) : bnxN m s = m (false, s) + m (true, s) := rfl

theorem bnx_coeff_subst (a b : ZMod d → K) (f : MvPowerSeries (ZMod d) K) (m : V2 d →₀ ℕ) :
    coeff m (subst (bnxA a b) f) = coeff (bnxN m) f *
      ∏ s, (a s ^ m (false, s) * b s ^ m (true, s) * ((m (false, s) + m (true, s)).choose (m (false, s)) : K)) := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero fun s => by simp [bnxA])]
  have hterm : ∀ dd : ZMod d →₀ ℕ, coeff m (dd.prod fun s e => bnxA a b s ^ e) =
      ∏ s, (if m (false, s) + m (true, s) = dd s then
        a s ^ m (false, s) * b s ^ m (true, s) * ((dd s).choose (m (false, s)) : K) else 0) := fun dd => by
    rw [Finsupp.prod_fintype _ _ fun _ => pow_zero _, bnx_coeff_prod]
    exact Finset.prod_congr rfl fun s _ => bnx_lin_pow_val (x := (false, s)) (y := (true, s)) (by simp) (a s) (b s) (dd s) _ _
  rw [finsum_eq_single _ (bnxN m)]
  · simp only [hterm, smul_eq_mul, bnxN_apply, ↓reduceIte]
  · intro dd hdd
    obtain ⟨s, hs⟩ : ∃ s, dd s ≠ bnxN m s := by by_contra hc; push Not at hc; exact hdd (Finsupp.ext hc)
    rw [hterm, Finset.prod_eq_zero (Finset.mem_univ s), smul_zero]
    split_ifs with h <;> [exact absurd (h.symm.trans (bnxN_apply m s).symm) hs; rfl]

theorem evenIndicator_series_binomial_form : (s1 : ZMod d → MvPowerSeries (V2 d) K) =
    bnxA (fun _ => 1) (fun s => if s.val % 2 = 0 then 1 else 0) := by
  have _ := NeZero.ne d; funext s; simp only [s1, bnxA]; split_ifs <;> simp

theorem zero_series_binomial_form : (s0 : ZMod d → MvPowerSeries (V2 d) K) = bnxA (fun _ => 1) (fun _ => 0) := by
  have _ := NeZero.ne d; funext s; simp [s0, bnxA]

theorem swapped_parity_series_binomial_form : (s2 : ZMod d → MvPowerSeries (V2 d) K) =
    bnxA (fun s => if s.val % 2 = 0 then 0 else 1) (fun s => if s.val % 2 = 0 then 1 else 0) := by
  have _ := NeZero.ne d; funext s; simp only [s2, bnxA]; split_ifs <;> simp

theorem oddIndicator_series_binomial_form : (s1' : ZMod d → MvPowerSeries (V2 d) K) =
    bnxA (fun _ => 1) (fun s => if s.val % 2 = 0 then 0 else 1) := by
  have _ := NeZero.ne d; funext s; simp only [s1', bnxA]; split_ifs <;> simp

theorem parity_series_binomial_form : (s2' : ZMod d → MvPowerSeries (V2 d) K) =
    bnxA (fun s => if s.val % 2 = 0 then 1 else 0) (fun s => if s.val % 2 = 0 then 0 else 1) := by
  have _ := NeZero.ne d; funext s; simp only [s2', bnxA]; split_ifs <;> simp

def bnxM (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) : V2 d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun x => if x.1 then n x.2 - k x.2 else k x.2

theorem bnxM_false (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (s : ZMod d) : bnxM n k (false, s) = k s := rfl

theorem bnxM_true (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (s : ZMod d) : bnxM n k (true, s) = n s - k s := rfl

theorem bnxN_bnxM (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (hk : ∀ s, k s ≤ n s) : bnxN (bnxM n k) = n := by
  ext s; rw [bnxN_apply, bnxM_false, bnxM_true]; have := hk s; omega

theorem bnx_degree_bnxM (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (hk : ∀ s, k s ≤ n s) : (bnxM n k).degree = n.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, bnxM_true, bnxM_false, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by have := hk s; omega
end Subst

section De
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]

theorem bnx_update_le (n : ZMod d →₀ ℕ) (s : ZMod d) (j : ℕ) (hj : j < n s) :
    ∀ t, Function.update (⇑n) s j t ≤ n t := fun t => by
  have _ := NeZero.ne d; rw [Function.update_apply]; split_ifs with h <;> [exact h ▸ hj.le; exact le_rfl]

theorem bnx_prod_choose (n : ZMod d →₀ ℕ) (s : ZMod d) (j : ℕ) (hj : j < n s) (e : ZMod d → K) (he : e s = 1) :
    ∏ t, ((1 : K) ^ Function.update (⇑n) s j t * e t ^ (n t - Function.update (⇑n) s j t) *
      ((Function.update (⇑n) s j t + (n t - Function.update (⇑n) s j t)).choose
        (Function.update (⇑n) s j t) : K)) = ((n s).choose j : K) := by
  rw [Finset.prod_eq_single s]
  · simp [he, Nat.add_sub_cancel' hj.le]
  · exact fun t _ hts => by simp [hts]
  · exact fun h => absurd (Finset.mem_univ s) h

private theorem deriv_binomial_coeff (P : ZMod d → Prop) [DecidablePred P]
    (be : MvPowerSeries (ZMod d) K) (n : ZMod d →₀ ℕ) (s : ZMod d) (hs : P s)
    (j : ℕ) (hj : j < n s) (hpos : 0 < j ∨ ∃ t : ZMod d, P t ∧ t ≠ s ∧ n t ≠ 0) :
    coeff (bnxM n (Function.update (⇑n) s j))
      (subst (bnxA (fun _ => 1) (fun t => if P t then 1 else 0)) be - subst (bnxA (fun _ => 1) (fun _ => 0)) be -
        subst (bnxA (fun t => if P t then 0 else 1) (fun t => if P t then 1 else 0)) be) =
      coeff n be * ((n s).choose j : K) := by
  rw [map_sub, map_sub, bnx_coeff_subst, bnx_coeff_subst, bnx_coeff_subst, bnxN_bnxM n _ (bnx_update_le n s j hj)]
  simp only [bnxM_false, bnxM_true]
  rw [bnx_prod_choose n s j hj (fun t => if P t then (1 : K) else 0) (by simp [hs]),
    Finset.prod_eq_zero (Finset.mem_univ s) (by simp [zero_pow (by omega : n s - j ≠ 0)]), mul_zero, sub_zero]
  rcases hpos with hj0 | ⟨t, ht, hts, hnt⟩
  · rw [Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs, hj0.ne']), mul_zero, sub_zero]
  · rw [Finset.prod_eq_zero (Finset.mem_univ t) (by simp [hts, ht, hnt]), mul_zero, sub_zero]

theorem evenDerivative_binomial_coeff (be : MvPowerSeries (ZMod d) K) (n : ZMod d →₀ ℕ) (s : ZMod d)
    (hs : s.val % 2 = 0) (j : ℕ) (hj : j < n s) (hpos : 0 < j ∨ ∃ t : ZMod d, t.val % 2 = 0 ∧ t ≠ s ∧ n t ≠ 0) :
    coeff (bnxM n (Function.update (⇑n) s j)) (de1 be) = coeff n be * ((n s).choose j : K) := by
  rw [de1, evenIndicator_series_binomial_form, zero_series_binomial_form, swapped_parity_series_binomial_form]
  exact deriv_binomial_coeff (fun t => t.val % 2 = 0) be n s hs j hj hpos

theorem oddDerivative_binomial_coeff (be : MvPowerSeries (ZMod d) K) (n : ZMod d →₀ ℕ) (s : ZMod d)
    (hs : s.val % 2 ≠ 0) (j : ℕ) (hj : j < n s) (hpos : 0 < j ∨ ∃ t : ZMod d, t.val % 2 ≠ 0 ∧ t ≠ s ∧ n t ≠ 0) :
    coeff (bnxM n (Function.update (⇑n) s j)) (de2 be) = coeff n be * ((n s).choose j : K) := by
  rw [de2, oddIndicator_series_binomial_form, zero_series_binomial_form, parity_series_binomial_form]
  simpa only [ne_eq, ite_not] using deriv_binomial_coeff (fun t => t.val % 2 ≠ 0) be n s hs j hj hpos
end De

section NormNat
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem bnx_norm_one {l : ℕ} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (B : ℕ) (hB : ¬ l ∣ B) : 1 ≤ ‖(B : K)‖ := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 (hl.coprime_iff_not_dvd.2 hB)
  have h1 : (u : K) * l + v * B = 1 := by simpa using congrArg (Int.cast : ℤ → K) huv
  have key : (1 : ℝ) ≤ max (‖(u : K)‖ * ‖(l : K)‖) (‖(v : K)‖ * ‖(B : K)‖) := by
    simpa [norm_mul, h1] using IsUltrametricDist.norm_add_le_max ((u : K) * l) ((v : K) * B)
  rcases le_max_iff.1 key with h | h
  · linarith [mul_le_of_le_one_left (norm_nonneg (l : K)) (IsUltrametricDist.norm_intCast_le_one K u)]
  · exact h.trans (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one K v))

theorem bnx_norm_ge {l : ℕ} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (B : ℕ) (hB0 : B ≠ 0)
    (hB : ¬ l ^ 2 ∣ B) : ‖(l : K)‖ ≤ ‖(B : K)‖ := by
  let _ := hB0; by_cases hd : l ∣ B
  · obtain ⟨B', rfl⟩ := hd; rw [Nat.cast_mul, norm_mul]
    exact le_mul_of_one_le_right (norm_nonneg _) (bnx_norm_one hl hl1 B' fun h => hB (pow_two l ▸ mul_dvd_mul_left l h))
  · exact hl1.le.trans (bnx_norm_one hl hl1 B hd)
end NormNat

theorem bnx_choose_lucas {l : ℕ} (hl : l.Prime) (c : ℕ) : ∀ a : ℕ, (l ^ a * c).choose (l ^ a) ≡ c [MOD l] := by
  have := Fact.mk hl; intro a; induction a with
  | zero => simp [Nat.ModEq]
  | succ a ih =>
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := l * (l ^ a * c)) (k := l * l ^ a) (p := l)
    rw [Nat.mul_mod_right, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hl.pos,
      Nat.mul_div_cancel_left _ hl.pos, Nat.choose_self, one_mul] at h
    rw [pow_succ', mul_assoc]; exact h.trans ih

theorem bnx_choose_nonpow {l : ℕ} (hl : l.Prime) (m : ℕ) (hm0 : m ≠ 0) (hm : ∀ e, m ≠ l ^ e) :
    ∃ j, 0 < j ∧ j < m ∧ ¬ l ∣ m.choose j := by
  obtain ⟨v, c, hc, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 l hl.ne_one
  have hc0 : c ≠ 0 := fun h => hm0 (by simp [h]); have hc1 : c ≠ 1 := fun h => hm v (by simp [h])
  refine ⟨l ^ v, pow_pos hl.pos v, lt_mul_of_one_lt_right (pow_pos hl.pos v) (by omega), fun hd => ?_⟩
  exact hc (Nat.modEq_zero_iff_dvd.1 ((bnx_choose_lucas hl c v).symm.trans (Nat.modEq_zero_iff_dvd.2 hd)))

theorem bnx_choose_pow {l : ℕ} (hl : l.Prime) (e : ℕ) (he : 1 ≤ e) :
    0 < l ^ (e - 1) ∧ l ^ (e - 1) < l ^ e ∧ (l ^ e).choose (l ^ (e - 1)) ≠ 0 ∧
      ¬ l ^ 2 ∣ (l ^ e).choose (l ^ (e - 1)) := by
  have hlp := hl.pos; have hk0 : 0 < l ^ (e - 1) := pow_pos hlp _
  have hN : l ^ e = l * l ^ (e - 1) := by rw [← pow_succ', Nat.sub_add_cancel he]
  have hlt : l ^ (e - 1) < l ^ e := hN ▸ lt_mul_of_one_lt_left hk0 hl.one_lt
  refine ⟨hk0, hlt, (Nat.choose_pos hlt.le).ne', fun hdiv => ?_⟩
  have hC : (l ^ e).choose (l ^ (e - 1)) = l * (l ^ e - 1).choose (l ^ (e - 1) - 1) := by
    apply Nat.eq_of_mul_eq_mul_right hk0
    have hid := Nat.add_one_mul_choose_eq (l ^ e - 1) (l ^ (e - 1) - 1)
    have e1 : l ^ e - 1 + 1 = l ^ e := by omega
    have e2 : l ^ (e - 1) - 1 + 1 = l ^ (e - 1) := by omega
    rw [e1, e2] at hid; rw [← hid, hN]; ring
  rw [hC, pow_two] at hdiv; have h7 := Nat.dvd_of_mul_dvd_mul_left hlp hdiv
  have hmod1 : ∀ b : ℕ, (l ^ (b + 1) - 1).choose (l ^ b - 1) ≡ 1 [MOD l] := by
    have := Fact.mk hl
    have hdm : ∀ a : ℕ, (l ^ (a + 1) - 1) % l = l - 1 ∧ (l ^ (a + 1) - 1) / l = l ^ a - 1 := fun a => by
      have hs : l ^ (a + 1) - 1 = (l - 1) + l * (l ^ a - 1) := by
        have : l ≤ l * l ^ a := Nat.le_mul_of_pos_right l (pow_pos hlp a); rw [pow_succ', Nat.mul_sub_one]; omega
      rw [hs, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hlp,
        Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega), zero_add]; exact ⟨rfl, rfl⟩
    intro b; induction b with
    | zero => simp [Nat.ModEq]
    | succ b ih =>
      have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
        (n := l ^ (b + 2) - 1) (k := l ^ (b + 1) - 1) (p := l)
      rw [(hdm (b + 1)).1, (hdm b).1, (hdm (b + 1)).2, (hdm b).2, Nat.choose_self, one_mul] at h
      exact h.trans ih
  have hm := hmod1 (e - 1); rw [Nat.sub_add_cancel he] at hm
  exact hl.not_dvd_one (Nat.modEq_zero_iff_dvd.1 (hm.symm.trans (Nat.modEq_zero_iff_dvd.2 h7)))

theorem bnx_pow_reduce (l d x : ℕ) (hl : 1 ≤ l) : l ^ x ≡ l ^ (x % d) [MOD l ^ d - 1] := by
  have h1 : l ^ d ≡ 1 [MOD l ^ d - 1] := ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hl)).2 dvd_rfl).symm
  calc l ^ x = (l ^ d) ^ (x / d) * l ^ (x % d) := by rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    _ ≡ 1 ^ (x / d) * l ^ (x % d) [MOD l ^ d - 1] := (h1.pow _).mul_right _
    _ = l ^ (x % d) := by rw [one_pow, one_mul]

theorem bnx_pow_mod (l d x y : ℕ) (hl : 3 ≤ l) (hd : 1 ≤ d) (h : l ^ x ≡ l ^ y [MOD l ^ d - 1]) : x % d = y % d := by
  have h' := (bnx_pow_reduce l d x (by omega)).symm.trans (h.trans (bnx_pow_reduce l d y (by omega)))
  have hlt : ∀ k < d, l ^ k < l ^ d - 1 := fun k hk => by
    have h1 : l ^ k ≤ l ^ (d - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 3 * l ^ (d - 1) ≤ l ^ d := by
      rw [show l ^ d = l * l ^ (d - 1) by rw [← pow_succ', Nat.sub_add_cancel hd]]
      exact Nat.mul_le_mul_right _ hl
    have h3 : 1 ≤ l ^ (d - 1) := Nat.one_le_pow _ _ (by omega); omega
  unfold Nat.ModEq at h'
  rw [Nat.mod_eq_of_lt (hlt _ (Nat.mod_lt _ (by omega))), Nat.mod_eq_of_lt (hlt _ (Nat.mod_lt _ (by omega)))] at h'
  exact Nat.pow_right_injective (by omega) h'

theorem bnx_torus_cong {K : Type u} [Field K] (l d : ℕ) [NeZero d] (hl : l.Prime) (hl3 : 3 ≤ l)
    (hd2 : 2 ≤ d) (hde : Even d) (ζ : K) (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
    (be : MvPowerSeries (ZMod d) K) (htor : subst (torus l ζ) be = be)
    (s s' : ZMod d) (hs : s.val % 2 = 0) (hs' : s'.val % 2 ≠ 0) (α β : ℕ)
    (hc : coeff (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) be ≠ 0) :
    s + (α : ZMod d) = s' + (β : ZMod d) := by
  let _ := PLift.up hl; let _ := PLift.up hde
  have htor_prod : ∀ dd : ZMod d →₀ ℕ, (dd.prod fun t e => (torus l ζ t : MvPowerSeries (ZMod d) K) ^ e) =
      C (∏ t, (ζ ^ lw l t) ^ dd t) * monomial dd 1 := fun dd => by
    rw [Finsupp.prod_fintype _ _ fun _ => pow_zero _]
    simp only [torus, mul_pow, ← map_pow, Finset.prod_mul_distrib, map_prod]
    suffices ∀ S : Finset (ZMod d), ∏ t ∈ S, (X t ^ dd t : MvPowerSeries (ZMod d) K) =
        monomial (∑ t ∈ S, Finsupp.single t (dd t)) 1 by
      rw [this, show ∑ t, Finsupp.single t (dd t) = dd by ext; simp]
    exact fun S => Finset.induction_on S (by simp [monomial_zero_eq_C_apply]) fun a S ha ih => by
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, X_pow_eq, monomial_mul_monomial, one_mul]
  have hk0 : 0 < l ^ d - 1 := by have := Nat.le_self_pow (by omega : d ≠ 0) l; omega
  have hss : s ≠ s' := fun e => hs' (e ▸ hs)
  have hcoef := congrArg (coeff (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β))) htor
  rw [coeff_subst (hasSubst_of_constantCoeff_zero fun t => by simp [torus]),
    finsum_eq_single _ (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β))] at hcoef
  swap
  · intro dd hdd; rw [htor_prod, coeff_C_mul, coeff_monomial]; simp [Ne.symm hdd]
  rw [htor_prod, coeff_C_mul, coeff_monomial] at hcoef; simp only [↓reduceIte, mul_one, smul_eq_mul] at hcoef
  have hprod := mul_left_cancel₀ hc (hcoef.trans (mul_one _).symm)
  rw [Finset.prod_eq_mul s s' hss (fun t _ ht => by simp [Ne.symm ht.1, Ne.symm ht.2])
    (fun h => absurd (Finset.mem_univ s) h) (fun h => absurd (Finset.mem_univ s') h)] at hprod
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hss,
    Finsupp.single_eq_of_ne (Ne.symm hss), add_zero, zero_add] at hprod
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ (hζ.ne_zero hk0.ne'),
    hζ.zpow_eq_one_iff_dvd, show lw l s = (l : ℤ) ^ s.val by simp [lw, hs],
    show lw l s' = -(l : ℤ) ^ s'.val by simp [lw, hs']] at hprod
  have hmod : l ^ (s.val + α) ≡ l ^ (s'.val + β) [MOD l ^ d - 1] := by
    rw [Nat.modEq_iff_dvd]; convert dvd_neg.2 hprod using 1; push_cast; ring
  simpa [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_zmod_val] using
    congrArg (Nat.cast : ℕ → ZMod d) (bnx_pow_mod l d _ _ hl3 (by omega) hmod)

theorem bnx_dot_const {ι : Type*} (n : ι →₀ ℕ) (c : ℝ) : dot n (fun _ => c) = (n.degree : ℝ) * c := by
  simp [dot, Finsupp.sum, ← Finset.sum_mul, Finsupp.degree_apply]

section Sides
variable {K : Type u} [NormedField K] {d : ℕ} [NeZero d]

theorem bnx_sideE (be : MvPowerSeries (ZMod d) K) (pi r w : ℝ) (h1 : WtGe pi (fun _ => r) w (de1 be))
    (n : ZMod d →₀ ℕ) (s : ZMod d) (hs : s.val % 2 = 0) (j : ℕ) (hj : j < n s)
    (hpos : 0 < j ∨ ∃ t : ZMod d, t.val % 2 = 0 ∧ t ≠ s ∧ n t ≠ 0) :
    ‖coeff n be‖ * ‖((n s).choose j : K)‖ ≤ pi ^ (w - dot n (fun _ => r)) := by
  simpa [MonoWtGe, evenDerivative_binomial_coeff be n s hs j hj hpos, norm_mul, bnx_dot_const,
    bnx_degree_bnxM n _ (bnx_update_le n s j hj)] using h1 (bnxM n (Function.update (⇑n) s j))

theorem bnx_sideO (be : MvPowerSeries (ZMod d) K) (pi r w : ℝ) (h2 : WtGe pi (fun _ => r) w (de2 be))
    (n : ZMod d →₀ ℕ) (s : ZMod d) (hs : s.val % 2 ≠ 0) (j : ℕ) (hj : j < n s)
    (hpos : 0 < j ∨ ∃ t : ZMod d, t.val % 2 ≠ 0 ∧ t ≠ s ∧ n t ≠ 0) :
    ‖coeff n be‖ * ‖((n s).choose j : K)‖ ≤ pi ^ (w - dot n (fun _ => r)) := by
  simpa [MonoWtGe, oddDerivative_binomial_coeff be n s hs j hj hpos, norm_mul, bnx_dot_const,
    bnx_degree_bnxM n _ (bnx_update_le n s j hj)] using h2 (bnxM n (Function.update (⇑n) s j))
end Sides

theorem bnx_div {pi a b X v : ℝ} (h0 : 0 < pi) (hb : pi ^ v ≤ b) (ha : 0 ≤ a) (h : a * b ≤ X) : a ≤ X / pi ^ v :=
  (le_div_iff₀ (Real.rpow_pos_of_pos h0 v)).2 ((mul_le_mul_of_nonneg_left hb ha).trans h)

theorem bnx_side_cases {d : ℕ} {l : ℕ} (hl : l.Prime) (P : ZMod d → Prop) (n : ZMod d →₀ ℕ) (h : ∃ s, P s ∧ n s ≠ 0) :
    (∃ s j, P s ∧ j < n s ∧ (0 < j ∨ ∃ t, P t ∧ t ≠ s ∧ n t ≠ 0) ∧ ¬ l ∣ (n s).choose j) ∨
    (∃ s e, P s ∧ (∀ t, P t → t ≠ s → n t = 0) ∧ n s = l ^ e) := by
  obtain ⟨s, hs, hns⟩ := h
  by_cases hex : ∃ t, P t ∧ t ≠ s ∧ n t ≠ 0
  · exact Or.inl ⟨s, 0, hs, Nat.pos_of_ne_zero hns, Or.inr hex, by simpa using hl.not_dvd_one⟩
  · push Not at hex; by_cases hpow : ∃ e, n s = l ^ e
    · obtain ⟨e, he⟩ := hpow; exact Or.inr ⟨s, e, hs, hex, he⟩
    · push Not at hpow; obtain ⟨j, hj0, hjn, hjd⟩ := bnx_choose_nonpow hl (n s) hns hpow
      exact Or.inl ⟨s, j, hs, hjn, Or.inl hj0, hjd⟩

theorem bnx_degE_eq {d : ℕ} [NeZero d] (n : ZMod d →₀ ℕ) (s : ZMod d) (hs : s.val % 2 = 0)
    (hu : ∀ t : ZMod d, t.val % 2 = 0 → t ≠ s → n t = 0) : degE n = n s := by
  rw [degE, Finset.sum_eq_single s, ite_eq_left hs]
  · intro t _ hts; split_ifs with ht <;> [exact hu t ht hts; rfl]
  · exact fun h => absurd (Finset.mem_univ s) h

theorem bnx_degO_eq {d : ℕ} [NeZero d] (n : ZMod d →₀ ℕ) (s : ZMod d) (hs : s.val % 2 ≠ 0)
    (hu : ∀ t : ZMod d, t.val % 2 ≠ 0 → t ≠ s → n t = 0) : degO n = n s := by
  rw [degO, Finset.sum_eq_single s, ite_eq_right hs]
  · intro t _ hts; split_ifs with ht <;> [rfl; exact hu t ht hts]
  · exact fun h => absurd (Finset.mem_univ s) h

theorem bnx_exE {d : ℕ} [NeZero d] (n : ZMod d →₀ ℕ) (h : 0 < degE n) :
    ∃ s : ZMod d, s.val % 2 = 0 ∧ n s ≠ 0 := by
  obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  split_ifs at hs with he <;> [exact ⟨s, he, hs⟩; exact absurd rfl hs]

theorem bnx_exO {d : ℕ} [NeZero d] (n : ZMod d →₀ ℕ) (h : 0 < degO n) :
    ∃ s : ZMod d, s.val % 2 ≠ 0 ∧ n s ≠ 0 := by
  obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  split_ifs at hs with he <;> [exact absurd rfl hs; exact ⟨s, he, hs⟩]

theorem binomial_coefficient_extraction : BinomExtract.{u} := by
  intro K _ _ _ l d _ hl ⟨m, hm⟩ hd2 hde hl1 ζ hζ be htor hlow h1 h2
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  let r := rho l; let w : ℝ := 1 / ((l : ℝ) - 1)
  have key : ∀ n : ZMod d →₀ ℕ, coeff n be ≠ 0 →
      MonoWtGe ‖(l : K)‖ (fun _ => r) w n (coeff n be) ∨
        (IsBiPower l n ∧ MonoWtGe ‖(l : K)‖ (fun _ => r) (w - 1) n (coeff n be)) := fun n hn => by
    obtain ⟨hE, hO, hEO⟩ := hlow n hn; have hc0 := norm_nonneg (coeff n be); unfold MonoWtGe
    rcases bnx_side_cases hl (fun s : ZMod d => s.val % 2 = 0) n (bnx_exE n hE) with
      ⟨s, j, hs, hj, hpos, hnd⟩ | ⟨s, α, hs, hu, hα⟩
    · exact Or.inl ((le_mul_of_one_le_right hc0 (bnx_norm_one hl hl1 _ hnd)).trans
        (bnx_sideE be _ _ _ h1 n s hs j hj hpos))
    rcases bnx_side_cases hl (fun s : ZMod d => s.val % 2 ≠ 0) n (bnx_exO n hO) with
      ⟨s', j, hs', hj, hpos, hnd⟩ | ⟨s', β, hs', hu', hβ⟩
    · exact Or.inl ((le_mul_of_one_le_right hc0 (bnx_norm_one hl hl1 _ hnd)).trans
        (bnx_sideO be _ _ _ h2 n s' hs' j hj hpos))
    have hss : s ≠ s' := fun e => hs' (e ▸ hs)
    have hneq : n = Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β) := by
      ext t; rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
      by_cases ht : t.val % 2 = 0
      · by_cases hts : t = s
        · subst hts; simp [hss.symm, hα]
        · simp [Ne.symm hts, show s' ≠ t from fun e => hs' (e ▸ ht), hu t ht hts]
      · by_cases hts : t = s'
        · subst hts; simp [hss, hβ]
        · simp [Ne.symm hts, show s ≠ t from fun e => ht (e ▸ hs), hu' t ht hts]
    have hαβ : α ≠ 0 ∨ β ≠ 0 := by
      by_contra hc; rw [not_or, not_ne_iff, not_ne_iff] at hc
      exact hEO ⟨by simp [bnx_degE_eq n s hs hu, hα, hc.1], by simp [bnx_degO_eq n s' hs' hu', hβ, hc.2]⟩
    have hcong := bnx_torus_cong l d hl hl3 hd2 hde ζ hζ be htor s s' hs hs' α β (hneq ▸ hn)
    refine Or.inr ⟨⟨s, s', α, β, hs, Nat.mod_two_ne_zero.1 hs', hαβ, hcong, hneq⟩, ?_⟩
    have hpow_bd : ∀ {γ : ℕ}, γ ≠ 0 →
        (∀ j, j < l ^ γ → 0 < j → ‖coeff n be‖ * ‖((l ^ γ).choose j : K)‖ ≤ ‖(l : K)‖ ^ (w - dot n (fun _ => r))) →
        ‖coeff n be‖ ≤ ‖(l : K)‖ ^ (w - 1 - dot n (fun _ => r)) := fun hγ hside => by
      obtain ⟨hj0, hjlt, hCne, hC2⟩ := bnx_choose_pow hl _ (Nat.one_le_iff_ne_zero.2 hγ)
      have hb := (mul_le_mul_of_nonneg_left (bnx_norm_ge hl hl1 _ hCne hC2) hc0).trans (hside _ hjlt hj0)
      have h3 := bnx_div (v := 1) hpi0 (Real.rpow_one _).le hc0 hb
      rwa [← Real.rpow_sub hpi0, show w - dot n (fun _ => r) - 1 = w - 1 - dot n (fun _ => r) by ring] at h3
    rcases hαβ with hα0 | hβ0
    · exact hpow_bd hα0 fun j hj hj0 => hα ▸ bnx_sideE be _ _ _ h1 n s hs j (hα.symm ▸ hj) (Or.inl hj0)
    · exact hpow_bd hβ0 fun j hj hj0 => hβ ▸ bnx_sideO be _ _ _ h2 n s' hs' j (hβ.symm ▸ hj) (Or.inl hj0)
  refine ⟨fun n => (em (coeff n be = 0)).elim (fun hn => by simp [MonoWtGe, hn]; positivity) fun hn =>
    (key n hn).elim (fun h => h.trans (Real.rpow_le_rpow_of_exponent_ge hpi0 hl1.le (by linarith))) And.right,
    fun n hnb => (em (coeff n be = 0)).elim (fun hn => by simp [MonoWtGe, hn]; positivity) fun hn =>
      (key n hn).resolve_right fun hb => hnb hb.1⟩

end Formalism.DworkPowerSeriesWeights
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.GaussJetBounds.GaussJetProofs.SwappedParitySeriesBinomialForm =====

-- ===== clump member: Formalism.GaussJetBounds.OneLetterRadius =====
-- clump-header: {"m": "Formalism.GaussJetBounds.OneLetterRadius", "h": "module\n\npublic import Formalism.GaussJetBounds.Statement\npublic import Formalism.GaussJetBounds.GaussJetProofs.AsmOne\npublic import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffEvenDerivativeEqZero\npublic import Formalism.GaussJetBounds.GaussJetProofs.ExistsNeZeroOfFinsumNeZero\npublic import Formalism.GaussJetBounds.GaussJetProofs.LogStep\nimport Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison\npublic import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat\npublic import Formalism.GaussJetBounds.GaussJetProofs.OneLetterRadiusIdentity\nimport Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound\npublic import Formalism.GaussJetBounds.GaussJetProofs.SwappedParitySeriesBinomialForm\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

universe u v

namespace Formalism.DworkPowerSeriesWeights

theorem lemmaS : LemmaS.{u} :=
  lemmaS_of generalized_log_weight generalized_log_inverse logarithm_weight_comparison substitution_weight_bound exponential_derivative_inverse
    weightQuantization logarithm_weight_induction binomial_coefficient_extraction

theorem oneLetterR : OneLetterR.{u, v} :=
  oneLetterR_of lemmaS generalized_log_weight logarithm_weight_comparison substitution_weight_bound substitution_weight_bound radical_weight_monotone
    multiplicative_weight_le exponential_weight_le factorial_valuation_bound oneLetterRadiusIdentity

end Formalism.DworkPowerSeriesWeights
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.GaussJetBounds.OneLetterRadius =====
