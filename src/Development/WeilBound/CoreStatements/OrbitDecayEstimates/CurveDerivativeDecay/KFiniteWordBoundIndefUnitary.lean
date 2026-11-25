module

public import Development.WeilBound.CoreStatements.BranchingTraces.HeBranching
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeExpK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeHW
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCoreA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothA

@[expose] public section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open scoped InnerProductSpace

namespace CompanionTheory.Lime.T3

section Alg

variable {n : ℕ} {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}

theorem re_term (hU : IsInfUnitary ε E) (a b : Fin n) (x : M) :
    RCLike.re (inner ℂ ((E a b * E b a) x) x) = (if ε b = ε a then 1 else -1) * ‖E b a x‖ ^ 2 := by
  rw [mul_apply_eq_comp, hU a b, inner_self_eq_norm_sq_to_K]
  unfold adjSign
  by_cases h : ε b = ε a
  · simp [h, ← Complex.ofReal_pow]
  · simp [h, Ne.symm h, ← Complex.ofReal_pow]

theorem sum_sq_eq (hU : IsInfUnitary ε E) (x : M) :
    ∑ a, ∑ b, ‖E b a x‖ ^ 2 =
      2 * RCLike.re (inner ℂ (casimirK ε E x) x) - RCLike.re (inner ℂ (casimir E x) x) := by
  simp only [casimir, casimirK, LinearMap.sum_apply, sum_inner, map_sum,
    Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : ε a = ε b
  · simp only [h, ite_true, re_term hU a b x]; ring
  · simp only [Ne.symm h, ite_false, LinearMap.zero_apply, inner_zero_left, map_zero, re_term hU a b x]; ring

theorem norm_actM_le (X : Matrix (Fin n) (Fin n) ℂ) (hX : Formalism.REAL.hs X ≤ 1) (x : M) {C : ℝ} (hC : 0 ≤ C)
    (h : ∑ a, ∑ b, ‖E b a x‖ ^ 2 ≤ C ^ 2) : ‖actM E X x‖ ≤ C := by
  have hS : ‖actM E X x‖ ≤ ∑ a, ∑ b, ‖X a b‖ * ‖E a b x‖ := by
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
      (le_of_eq (Finset.sum_congr rfl fun b _ => norm_smul _ _)))
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
    (fun p => ‖X p.1 p.2‖) (fun p => ‖E p.1 p.2 x‖)
  simp only [Fintype.sum_prod_type] at hCS
  have hsq : (∑ a, ∑ b, ‖X a b‖ * ‖E a b x‖) ^ 2 ≤ C ^ 2 :=
    hCS.trans <| (mul_le_mul hX (Finset.sum_comm.trans_le h) (by positivity) zero_le_one).trans_eq (one_mul _)
  exact hS.trans (le_of_sq_le_sq hsq hC)

theorem nsq_le {u : Fin n → ℝ} {c : ℝ} (h : ∀ a, |u a| ≤ c) : nsq u ≤ n * c ^ 2 := by
  unfold nsq dot
  calc ∑ a, u a * u a ≤ ∑ _a : Fin n, c ^ 2 := Finset.sum_le_sum fun a _ => by
        rw [← sq, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h a) 2
    _ = n * c ^ 2 := by simp

theorem abs_rhoN_le' (a : Fin n) : |rhoN ε a| ≤ n / 2 := by
  have key : ∀ s t : Finset (Fin n), |(((s.card : ℕ) : ℝ) - ((t.card : ℕ) : ℝ)) / 2| ≤ n / 2 := fun s t => by
    have h1 : ((s.card : ℕ) : ℝ) ≤ n := by exact_mod_cast (Finset.card_le_univ s).trans (by simp)
    have h2 : ((t.card : ℕ) : ℝ) ≤ n := by exact_mod_cast (Finset.card_le_univ t).trans (by simp)
    rw [abs_le]; constructor <;> linarith
  exact key _ _

theorem abs_rho_le (a : Fin n) : |rho n a| ≤ n / 2 := by
  unfold rho
  have h1 : ((a : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt a.isLt
  have h2 : (0 : ℝ) ≤ (a : ℕ) := Nat.cast_nonneg _
  rw [abs_le]; constructor <;> linarith

private theorem abs_lowK_add_rhoC_le {lam : Fin n → ℝ} {B : ℝ} (hB : ∀ a, |lam a| ≤ B) (a : Fin n) :
    |(lowK ε lam + rhoC ε) a| ≤ B + n / 2 := by
  have e : (lowK ε lam + rhoC ε) a = lam a + rhoN ε a := by simp only [lowK, Pi.add_apply, Pi.sub_apply]; ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add (hB a) (abs_rhoN_le' a))

private theorem re_inner_smul_real (c : ℝ) (x : M) :
    RCLike.re (inner ℂ ((c : ℂ) • x) x) = c * ‖x‖ ^ 2 := by
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- Gap-free Cartan-splitting Casimir energy bound on the lowest K-type (`layer 0`):
`∑ a b, ‖E b a x‖^2 ≤ 2 * n * (B + n)^2 * ‖x‖^2`, valid in every discrete-series chamber
with zero weight-gap assumption. -/
theorem lowestKType_energy_le {lam : Fin n → ℝ} {B : ℝ} (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    {V : Submodule ℂ M} (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hB : ∀ a, |lam a| ≤ B) (hB0 : 0 ≤ B)
    {x : M} (hx : x ∈ V) :
    ∑ a, ∑ b, ‖E b a x‖ ^ 2 ≤ 2 * n * (B + n) ^ 2 * ‖x‖ ^ 2 := by
  have hK := re_inner_casimirK_layer_le hE hU hV 0 hx
  simp only [Nat.cast_zero, mul_zero, add_zero, Real.sq_sqrt (_root_.ReciprocityTheory.ChartRestriction.DS.nsq_nonneg' _)] at hK
  rw [sum_sq_eq hU x, hc x hx, re_inner_smul_real]
  have hN := nsq_le (abs_lowK_add_rhoC_le (ε := ε) hB)
  have hrho := nsq_le (fun a => abs_rho_le (n := n) a)
  have hcoef : 2 * (nsq (lowK ε lam + rhoC ε) - nsq (rhoC ε)) - casVal lam ≤ 2 * n * (B + n) ^ 2 := by
    have : casVal lam = nsq lam - nsq (rho n) := rfl
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hpoly : 2 * (B + (n : ℝ) / 2) ^ 2 + ((n : ℝ) / 2) ^ 2 ≤ 2 * (B + n) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hpoly hn0
    linarith [_root_.ReciprocityTheory.ChartRestriction.DS.nsq_nonneg' lam, _root_.ReciprocityTheory.ChartRestriction.DS.nsq_nonneg' (rhoC ε)]
  have h1 : 2 * RCLike.re (inner ℂ (casimirK ε E x) x) - casVal lam * ‖x‖ ^ 2 ≤
      (2 * (nsq (lowK ε lam + rhoC ε) - nsq (rhoC ε)) - casVal lam) * ‖x‖ ^ 2 := by linarith
  exact h1.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))

theorem layer_bound {lam : Fin n → ℝ} {B : ℝ} (hE : IsGlRep E) (hU : IsInfUnitary ε E) {V : Submodule ℂ M}
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hn : 1 ≤ n)
    (hB : ∀ a, |lam a| ≤ B) (hnB : (n : ℝ) ≤ 4 * B) {k S : ℕ} (hk : k ≤ S) {x : M} (hx : x ∈ layer ε E V k) :
    ∑ a, ∑ b, ‖E b a x‖ ^ 2 ≤ (8 * Real.sqrt n * (B + S) * ‖x‖) ^ 2 := by
  have hcas : casimir E x = (casVal lam : ℂ) • x := casimir_genSub hE hc x (layer_le_genSub k hx)
  have hK := re_inner_casimirK_layer_le hE hU hV k hx
  rw [sum_sq_eq hU x, hcas, re_inner_smul_real]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hB0 : 0 ≤ B := by linarith
  have hS : (k : ℝ) ≤ S := by exact_mod_cast hk
  set s := Real.sqrt n
  have hs2 : s ^ 2 = n := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 hn1
  have hsN : Real.sqrt (nsq (lowK ε lam + rhoC ε)) ≤ s * (B + n / 2) :=
    (Real.sqrt_le_sqrt (by rw [mul_pow, hs2]; exact nsq_le (abs_lowK_add_rhoC_le hB))).trans_eq
      (Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (by linarith)))
  have hrho := nsq_le (fun a => abs_rho_le (n := n) a)
  have hsq2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  set R := Real.sqrt (nsq (lowK ε lam + rhoC ε)) + Real.sqrt 2 * k
  have hR : R ≤ 3 * s * (B + S) := by
    have h1 : s * (B + n / 2) ≤ s * (3 * B) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2 : Real.sqrt 2 * k ≤ 2 * S := mul_le_mul hsq2 hS (Nat.cast_nonneg _) (by norm_num)
    have h3 : 2 * (S : ℝ) ≤ 2 * s * S := by nlinarith
    nlinarith
  have hmain : 2 * (R ^ 2 - nsq (rhoC ε)) - casVal lam ≤ 64 * n * (B + S) ^ 2 := by
    have hcasv : casVal lam = nsq lam - nsq (rho n) := rfl
    have hR2 : R ^ 2 ≤ 9 * n * (B + S) ^ 2 := by
      have h6 := pow_le_pow_left₀ (by positivity) hR 2
      rw [mul_pow, mul_pow, hs2] at h6; linarith
    have hrho' : nsq (rho n) ≤ 4 * n * (B + S) ^ 2 := by
      have h5 := pow_le_pow_left₀ (by positivity) (show (n : ℝ) / 2 ≤ 2 * (B + S) by linarith) 2
      nlinarith
    rw [hcasv]; nlinarith [_root_.ReciprocityTheory.ChartRestriction.DS.nsq_nonneg' lam, _root_.ReciprocityTheory.ChartRestriction.DS.nsq_nonneg' (rhoC ε)]
  calc _ ≤ (2 * (R ^ 2 - nsq (rhoC ε)) - casVal lam) * ‖x‖ ^ 2 := by linarith
    _ ≤ (64 * n * (B + S) ^ 2) * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hmain (sq_nonneg _)
    _ = (8 * s * (B + S) * ‖x‖) ^ 2 := by rw [mul_pow, mul_pow, mul_pow, hs2]; ring

theorem actM_mem_layer (hE : IsGlRep E) {V : Submodule ℂ M} (hV : IsKStableSub ε E V) (X : Matrix (Fin n) (Fin n) ℂ)
    {k : ℕ} {x : M} (hx : x ∈ layer ε E V k) : actM E X x ∈ layer ε E V (k + 1) := by
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (apply_mem_layer_succ hE hV a b hx)

end Alg

theorem le_four_mul {m : ℕ} {lam : Fin m → ℝ} {B : ℝ} (hm : 2 ≤ m) (hl : Formalism.QuantumDeterminants.IsHCParam lam)
    (hB : ∀ a, |lam a| ≤ B) : (m : ℝ) ≤ 4 * B := by
  obtain ⟨hanti, hint⟩ := hl
  have step : ∀ a b : Fin m, a < b → 1 ≤ lam a - lam b := fun a b hab => by
    obtain ⟨p, hp⟩ := hint a
    obtain ⟨q, hq⟩ := hint b
    have hpq : q < p := by exact_mod_cast (show (q : ℝ) < p by linarith [hanti hab])
    have h4 : (q : ℝ) + 1 ≤ p := by exact_mod_cast (show q + 1 ≤ p by omega)
    linarith
  have chain : ∀ k : ℕ, ∀ hk : k < m, (k : ℝ) ≤ lam ⟨0, by omega⟩ - lam ⟨k, hk⟩ := fun k => by
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have := step ⟨k, by omega⟩ ⟨k + 1, hk⟩ (by simp [Fin.lt_def])
      push_cast; linarith [ih (by omega)]
  have hc := chain (m - 1) (by omega)
  rw [Nat.cast_sub (by omega), Nat.cast_one] at hc
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  linarith [(abs_le.1 (hB ⟨0, by omega⟩)).2, (abs_le.1 (hB ⟨m - 1, by omega⟩)).1]

theorem stdGap_of {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} (hm : 1 ≤ m) (hl : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ}
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hh : 2 * (m : ℝ) ^ 3 + 1 ≤ h) : StdGap ε lam := by
  refine ⟨hl.1, h, hg, ?_⟩
  have hp : (pOf ε : ℝ) ≤ m := by exact_mod_cast (Finset.card_le_univ _).trans (by simp)
  have hq : (qOf ε : ℝ) ≤ m := by exact_mod_cast (Finset.card_le_univ _).trans (by simp)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpq := mul_le_mul hp hq (Nat.cast_nonneg _) (by linarith)
  have h1 : (m : ℝ) * pOf ε * qOf ε ≤ (m : ℝ) ^ 3 := by nlinarith
  have h3 : (0 : ℝ) < (m : ℝ) ^ 3 := by positivity
  linarith

theorem dsigC_eq_actM {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (Y : Matrix (Fin m) (Fin m) ℂ)
    (x : smD ε σ) : PI.DSInfCharCap.dsigC ε σ Y x = ((actM (smE ε σ) Y x : smD ε σ) : H) := by
  have hD := isDerivedOn_smE hσ
  have e1 : (1 / 2 : ℂ) • (Y + PI.DSInfCharCap.thetaJ ε Y) = S7.cpart1 ε Y := by
    unfold PI.DSInfCharCap.thetaJ S7.cpart1; rw [sub_eq_add_neg]; rfl
  have e2 : (1 / (2 * Complex.I)) • (Y - PI.DSInfCharCap.thetaJ ε Y) = S7.cpart2 ε Y := by
    unfold PI.DSInfCharCap.thetaJ S7.cpart2; rw [sub_neg_eq_add]; rfl
  show PI.PhMeasCore.dsig σ ((1 / 2 : ℂ) • (Y + PI.DSInfCharCap.thetaJ ε Y)) x +
      Complex.I • PI.PhMeasCore.dsig σ ((1 / (2 * Complex.I)) • (Y - PI.DSInfCharCap.thetaJ ε Y)) x = _
  rw [e1, e2]
  change dS σ (S7.cpart1 ε Y) x + Complex.I • dS σ (S7.cpart2 ε Y) x = _
  rw [dS_eq_actM hD (SmDerA.inG_cpart1 ε Y) x, dS_eq_actM hD (SmDerA.inG_cpart2 ε Y) x]
  conv_rhs => rw [SmDerA.cpart_decomp ε Y]
  rw [actM_add', actM_smul']
  simp

theorem exists_lowestKType_data {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hm : 1 ≤ m)
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hDS : Formalism.MainNotions.S.IsDS ε lam π)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (100 * (m : ℝ) ^ 3)) :
    ∃ V : Submodule ℂ (smD ε π),
      IsKIrrHW ε (smE ε π) (lowK ε lam) V ∧
      IsKStableSub ε (smE ε π) V ∧
      Submodule.map (smD ε π).subtype V = Formalism.MainNotions.S.lowKSub ε lam π ∧
      ∀ y ∈ V, casimir (smE ε π) y = (casVal lam : ℂ) • y := by
  have : CompleteSpace H := hDS.1
  have hπ : IsURepOn (UJset ε) π := hDS.2.2.1
  have hD := isDerivedOn_smE hπ
  have hGl : IsGlRep (smE ε π) := hD.glRep
  have hIU : IsInfUnitary ε (smE ε π) := isInfUnitary_of_isDerivedOn hπ hD
  have hm3 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hgap : 2 * (m : ℝ) ^ 3 + 1 ≤ 100 * (m : ℝ) ^ 3 := by linarith [one_le_pow₀ hm3 (n := 3)]
  obtain ⟨_, h', hg', hlt⟩ := stdGap_of hm hl hg hgap
  obtain ⟨hcasS, huniq, _, hsmooth, _⟩ := isDS_props_of_gap m ε lam hl h' hg' hlt H π hDS
  obtain ⟨S0, hS0⟩ := hDS.2.2.2.2.2.1
  have hsub : Formalism.MainNotions.S.lowKSub ε lam π = S0 := by
    have hset : {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε π (Formalism.QuantumDeterminants.lowK ε lam) S} = {S0} :=
      Set.ext fun S => ⟨fun h => huniq S S0 h hS0, fun h => h ▸ hS0⟩
    unfold Formalism.MainNotions.S.lowKSub; rw [hset, sSup_singleton]
  have hS0le : S0 ≤ smD ε π := fun u hu => (mem_smD_iff ε π u).2 (hsmooth S0 hS0.1 hS0.2.1 u hu)
  obtain ⟨w, hwS, hw0, hwk⟩ := exists_isKHWVec_of_isKTypeOf hπ hD hS0 hS0le
  let T : Submodule ℂ (smD ε π) := S0.comap (smD ε π).subtype
  have hTfd : FiniteDimensional ℂ T := by
    have := hS0.1
    exact Module.Finite.of_injective
      (((smD ε π).subtype.comp T.subtype).codRestrict S0 fun x => x.2)
      fun _ _ hab => Subtype.ext (Subtype.ext (congrArg (Subtype.val : S0 → H) hab))
  have hTst : IsKStableSub ε (smE ε π) T := isKStableSub_of_kStable hπ hD T hTfd fun k hk y hy =>
    ⟨⟨π k y, (mem_smD_iff ε π _).2 (IsSmoothVecU.kStable hπ hk ((mem_smD_iff ε π _).1 y.2))⟩,
      hS0.2.1 k hk _ hy, rfl⟩
  let V := kLowSpan ε (smE ε π) w
  have hVT : V ≤ T := kLowSpan_le hTst hwS
  have hVfd : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hVT
  have hVirr : IsKIrrHW ε (smE ε π) (lowK ε lam) V := kLowSpan_kIrrHW hGl hIU hwk hw0 hVfd
  have hVst : IsKStableSub ε (smE ε π) V := kLowSpan_kStable hGl hwk
  have hVk := kStable_of_isKStableSub hπ hD V hVfd hVst
  have hmapS : Submodule.map (smD ε π).subtype V = S0 := by
    have hle : Submodule.map (smD ε π).subtype V ≤ S0 := by rintro _ ⟨y, hy, rfl⟩; exact hVT hy
    rcases hS0.2.2.1 _ hle (by rintro g hg _ ⟨y, hy, rfl⟩; exact hVk g hg y hy) with h | h
    · exfalso
      have hwm : (w : H) ∈ Submodule.map (smD ε π).subtype V := ⟨w, self_mem_kLowSpan w, rfl⟩
      rw [h] at hwm
      exact hw0 (Subtype.ext ((Submodule.mem_bot ℂ).1 hwm))
    · exact h
  refine ⟨V, hVirr, hVst, hmapS.trans hsub.symm, fun y _ => Subtype.ext ?_⟩
  rw [← casU_eq_casimir hD y]
  exact hcasS y ((mem_smD_iff ε π _).1 y.2)

theorem kFiniteWordBound_indefUnitary : PositivityTheory.UnitaryDecomposition.WordBd := by
  unfold PositivityTheory.UnitaryDecomposition.WordBd
  intro m ε lam B H _ _ π hm hl hDS hB hg v hv
  have hm1 : 1 ≤ m := by omega
  have hπ : IsURepOn (UJset ε) π := hDS.2.2.1
  have hD := isDerivedOn_smE hπ
  have hGl : IsGlRep (smE ε π) := hD.glRep
  have hIU : IsInfUnitary ε (smE ε π) := isInfUnitary_of_isDerivedOn hπ hD
  obtain ⟨V, hVirr, hVst, hmapS, hcV⟩ := exists_lowestKType_data hm1 hl hDS hg
  rw [← hmapS] at hv
  obtain ⟨x0, hx0V, rfl⟩ := hv
  have hnB : (m : ℝ) ≤ 4 * B := le_four_mul hm hl hB
  refine ⟨fun g₀ hg₀ => ((mem_smD_iff ε π _).1 x0.2) g₀ hg₀, fun S W hlen hX => ?_⟩
  have hC0 : 0 ≤ 8 * Real.sqrt m * (B + S) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (by linarith [Nat.cast_nonneg (α := ℝ) S])
  have key : ∀ W' : List (Matrix (Fin m) (Fin m) ℂ), (∀ X ∈ W', Formalism.REAL.hs X ≤ 1) → ∀ (j : ℕ) (y : smD ε π),
      y ∈ layer ε (smE ε π) V j → j + W'.length ≤ S →
      ∃ z : smD ε π, z ∈ layer ε (smE ε π) V (j + W'.length) ∧
        (z : H) = PI.DSInfCharCap.dsigCW ε π W' y ∧ ‖z‖ ≤ (8 * Real.sqrt m * (B + S)) ^ W'.length * ‖y‖ := by
    intro W'
    induction W' with
    | nil => intro _ j y hy _; exact ⟨y, by simpa using hy, rfl, by simp⟩
    | cons X W' ih =>
      intro hXW j y hy hjl
      have hl' : j + W'.length ≤ S := by simp only [List.length_cons] at hjl; omega
      obtain ⟨z, hz, hze, hzn⟩ := ih (fun Y hY => hXW Y (List.mem_cons_of_mem _ hY)) j y hy hl'
      have hstep := norm_actM_le X (hXW X (List.mem_cons_self ..)) z (mul_nonneg hC0 (norm_nonneg _))
        (layer_bound hGl hIU hVirr hcV hm1 hB hnB hl' hz)
      refine ⟨actM (smE ε π) X z, by simpa [Nat.add_assoc] using actM_mem_layer hGl hVst X hz, ?_, ?_⟩
      · show _ = PI.DSInfCharCap.dsigC ε π X (PI.DSInfCharCap.dsigCW ε π W' y)
        rw [← hze, dsigC_eq_actM hπ X z]
      · calc ‖actM (smE ε π) X z‖ ≤ 8 * Real.sqrt m * (B + S) * ‖z‖ := hstep
          _ ≤ 8 * Real.sqrt m * (B + S) * ((8 * Real.sqrt m * (B + S)) ^ W'.length * ‖y‖) :=
            mul_le_mul_of_nonneg_left hzn hC0
          _ = (8 * Real.sqrt m * (B + S)) ^ (X :: W').length * ‖y‖ := by rw [List.length_cons, pow_succ]; ring
  obtain ⟨z, _, hze, hzn⟩ := key W hX 0 x0 hx0V (by simpa using hlen)
  show ‖PI.DSInfCharCap.dsigCW ε π W (x0 : H)‖ ≤ (8 * Real.sqrt m * (B + S)) ^ W.length * ‖(x0 : H)‖
  rwa [← hze]

end CompanionTheory.Lime.T3
