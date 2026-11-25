module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PartRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CharOfScalar
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTorusEigenformOfCompactTorusEigenvector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqMult
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PropCker
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PropCp
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpMul
import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbittAlg
import GroundTheory.LocalFields.UnramifiedHensel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section




section
open ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.PRep UpperTheory.V.Hi
namespace UpperTheory.V.Z.J.D.OrdinaryOrderOne
section General
variable {G V : Type} [CommGroup G] [AddCommGroup V] [Module ℂ V]
private theorem gen_map {V' : Type} [AddCommGroup V'] [Module ℂ V'] (F : Submodule ℂ V) {f : Module.End ℂ V}
    {g : Module.End ℂ V'} (p : V →ₗ[ℂ] V') (hF : ∀ v ∈ F, f v ∈ F) (h : ∀ v ∈ F, p (f v) = g (p v)) {c : ℂ} {v : V}
    (hv : v ∈ F) (hc : v ∈ f.maxGenEigenspace c) : p v ∈ g.maxGenEigenspace c := by
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hc
  refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨m, ?_⟩
  have key : ∀ (m : ℕ), ∀ v ∈ F, ((g - c • (1 : Module.End ℂ V')) ^ m) (p v) =
      p (((f - c • (1 : Module.End ℂ V)) ^ m) v) := by
    intro m
    induction m with
    | zero => intro v _; simp
    | succ m ih =>
      intro v hv
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih]
      · simp [h v hv]
      · exact sub_mem (hF v hv) (F.smul_mem c hv)
  rw [key m v hv, hm, map_zero]
private theorem eq_of_prod {n : ℕ} {a b : Fin n → ℂ} (hb : ∀ i, b i ≠ 0)
    (h : ∀ j, ∏ i with i ≤ j, a i = ∏ i with i ≤ j, b i) (j : Fin n) : a j = b j := by
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have e : (Finset.univ.filter fun i => i ≤ j) = insert j (Finset.univ.filter fun i => i < j) := by
      ext i; simp [le_iff_eq_or_lt]
    have := h j
    rw [e, Finset.prod_insert (by simp), Finset.prod_insert (by simp),
      Finset.prod_congr rfl fun i hi => ih i (Finset.mem_filter.1 hi).2] at this
    exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 fun i _ => hb i) this
end General
private theorem inj {G M J : Type} [Group G] (I : Iwa G) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ G M)
    (hs : I.Smooth π) (a : J → G) (ha : ∀ j, a j ∈ I.P) (μ : J → ℂ) (hμ : ∀ j, μ j ≠ 0) (l : List G)
    (hz : I.z = l.prod) (hl : ∀ x ∈ l, x = 1 ∨ ∃ j, x = a j) {v : M} (hv : v ∈ fixd π I.N)
    (hv' : ∀ j, v ∈ (I.uOp π (a j)).maxGenEigenspace (μ j)) (h0 : v ∈ I.jacKer π) : v = 0 := by
  let S : M → Prop := fun v => v ∈ fixd π I.N ∧ ∀ j, v ∈ (I.uOp π (a j)).maxGenEigenspace (μ j)
  have st : ∀ x ∈ I.P, ∀ v, S v → S (I.uOp π x v) := fun x hx v hv =>
    ⟨(uOpMul G I ℂ M π _ _ hx hx v hv.1).1, fun j =>
      gen_map (fixd π I.N) (I.uOp π x) (fun w hw => (uOpMul G I ℂ M π _ _ (ha j) hx w hw).1) (fun w hw => by
        rw [(uOpMul G I ℂ M π _ _ hx (ha j) w hw).2.1, (uOpMul G I ℂ M π _ _ (ha j) hx w hw).2.1,
          I.comm x (I.P_le x hx) _ (I.P_le _ (ha j))]) hv.1 (hv.2 j)⟩
  have h1 : (1 : G) ∈ I.P ∧ ∀ v, S v → I.uOp π 1 v = 0 → v = 0 := ⟨one_mem _, fun v hv h => by
    rwa [(uOpMul G I ℂ M π _ _ (one_mem _) (one_mem _) v hv.1).2.2.1] at h⟩
  have hg : I.z ∈ I.P ∧ ∀ v, S v → I.uOp π I.z v = 0 → v = 0 := by
    rw [hz]
    refine List.prod_induction (fun x => x ∈ I.P ∧ ∀ v, S v → I.uOp π x v = 0 → v = 0) ?_ h1 ?_
    · rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
      refine ⟨mul_mem hx hy, fun v hv h => hy' v hv (hx' _ (st y hy v hv) ?_)⟩
      rw [(uOpMul G I ℂ M π _ _ hx hy v hv.1).2.1, h]
    · intro x hx
      obtain rfl | ⟨j, rfl⟩ := hl x hx
      · exact h1
      · exact ⟨ha j, fun v hv h => by_contra fun hn =>
          hμ j (OrdB.eq_of_gen (h.trans (zero_smul ℂ v).symm) hn (hv.2 j)).symm⟩
  obtain ⟨m, hm⟩ := (propCker G I ℂ M π hs v hv).1 h0
  have key : ∀ (m : ℕ) (v : M), S v → (I.uOp π I.z ^ m) v = 0 → v = 0 := by
    intro m
    induction m with
    | zero => intro v _ h; simpa using h
    | succ m ih =>
      intro v hv h
      rw [pow_succ, Module.End.mul_apply] at h
      exact hg.2 v hv (ih _ (st _ hg.1 v hv) h)
  exact key m v ⟨hv, hv'⟩ hm
end UpperTheory.V.Z.J.D.OrdinaryOrderOne
open UpperTheory.V.Z.J.D
theorem UpperTheory.V.Z.J.D.dense_threshold_order_one :
    _root_.UpperTheory.V.Z.J.D.Ord1Alt := by
  intro H k _ _ _ _ n V _ _ π hπ hirr b φ μ _ ⟨α, hα, hμ⟩
  obtain ⟨hker, hsm, -, -, -, -, -, hidx, hz, -⟩ := glBridge k n V π
  have hq : (Nat.card 𝓀[k] : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hα0 : ∀ i : Fin n, (α i : ℂ) * ((Nat.card 𝓀[k] : ℂ) ^ (i : ℕ))⁻¹ ≠ 0 := fun i =>
    mul_ne_zero (α i).ne_zero (inv_ne_zero (pow_ne_zero _ hq))
  have hL : ∀ v ∈ locEig π b φ μ, v ∈ fixd π (glIwa k n).N ∧
      ∀ j : Fin n, v ∈ ((glIwa k n).uOp π (al k n (j + 1))).maxGenEigenspace (μ j) := fun v hv =>
    ⟨hv.1.1.1, (Submodule.mem_iInf _).1 hv.2⟩
  let p : V →ₗ[ℂ] Jacquet π (unipB k (Fin n)) := Submodule.mkQ _
  have hinj : ∀ v ∈ locEig π b φ μ, p v = 0 → v = 0 := fun v hv h => by
    refine OrdinaryOrderOne.inj _ π (hsm hπ) (fun j : Fin n => al k n (j + 1)) (fun j => al_mem k n _) μ
      (fun j => by rw [hμ]; exact Finset.prod_ne_zero_iff.2 fun i _ => hα0 i) _ hz (fun x hx => ?_) (hL v hv).1 (hL v hv).2
      (hker ▸ (Submodule.Quotient.mk_eq_zero _).1 h)
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hj
    rcases j with _ | j
    · left
      rw [al, upow, ← (diagT k (Fin n)).map_one]
      congr 1
      ext i
      simp
    · exact Or.inr ⟨⟨j, by omega⟩, rfl⟩
  by_cases hne : locEig π b φ μ = ⊥
  · rw [hne, rank_bot]; exact zero_le_one
  have hp : ∀ t v, jacB π t (p v) =
      (((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) t))⁻¹ : ℂˣ) : ℂ) • p (π (diagT k (Fin n) t) v) :=
    fun t v => UnramFixed.jacB_apply π t _
  let t : Fin n → Fin n → kˣ := fun j i => unif k ^ (if (i : ℕ) < j + 1 then 1 else 0 : ℤ)
  let c : Fin n → ℂ := fun j => ((Nat.card 𝓀[k] ^ ((j + 1) * (n - (j + 1))) : ℕ) : ℂ) *
    (deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) (t j)) : ℂ)
  let E : Submodule ℂ (Jacquet π (unipB k (Fin n))) :=
    ⨅ j : Fin n, Module.End.maxGenEigenspace (c j • jacB π (t j)) (μ j)
  have hEs : ∀ s, ∀ y ∈ E, jacB π s y ∈ E := fun s y hy => (Submodule.mem_iInf _).2 fun j =>
    OrdinaryOrderOne.gen_map ⊤ (jacB π s) (fun _ _ => trivial) (fun v _ => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul,
        Module.End.mul_apply]) trivial ((Submodule.mem_iInf _).1 hy j)
  have hpE : ∀ v ∈ locEig π b φ μ, p v ∈ E := fun v hv => (Submodule.mem_iInf _).2 fun j => by
    refine OrdinaryOrderOne.gen_map (fixd π (glIwa k n).N) p
      (fun w hw => (uOpMul _ _ ℂ V π _ _ (al_mem k n _) (al_mem k n 0) w hw).1) (fun w hw => ?_) (hL v hv).1 ((hL v hv).2 j)
    have h1 := propCp _ (glIwa k n) ℂ V π _ (al_mem k n (j + 1)) w hw
    rw [hker, hidx (j + 1) j.2] at h1
    have h2 : p _ = 0 := (Submodule.Quotient.mk_eq_zero _).2 h1
    rw [map_sub, map_smul, sub_eq_zero] at h2
    rw [h2, LinearMap.smul_apply, hp, smul_smul, mul_assoc, Units.mul_inv, mul_one]
    rfl
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hl : HasFiniteLength (jacB π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((H.loc.bz k).2.1 _ _ _ (points (Fin n)) _ π hπ (hasFiniteLength_of_isIrreducible hirr))
  haveI := GlobalTheory.TorusEigenform.secondCountableTopology_units k
  obtain ⟨ν, hνs, -, l, hl0, hle⟩ := OrdB.exists_form (isSmooth_jacB hπ) hl fun h => hx0 (hinj x hx h)
  obtain ⟨ψ, hψ, rfl⟩ : ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ torusChar ψ = ν := by
    refine ⟨fun i => ν.comp (MonoidHom.mulSingle (fun _ => kˣ) i),
      fun i => hνs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), MonoidHom.ext fun t => ?_⟩
    rw [torusChar_apply]
    conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
    rfl
  have hsq : IsSubquotient π (prinSeries ψ) := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hirr _ l hl0 hle
  obtain ⟨hfd, -, hmult⟩ := UpperTheory.V.AlgebraTools.jqMult H.loc.geo H.loc.bz k n V π ψ hπ hψ hsq
  obtain ⟨ω, rfl⟩ : ∃ ω : Fin n → kˣ →* ℂˣ, (fun i => ω i * absPow k (((n : ℂ) - 1) / 2)) = ψ :=
    ⟨fun i => ψ i * (absPow k (((n : ℂ) - 1) / 2))⁻¹, funext fun i => inv_mul_cancel_right _ _⟩
  set ψ : Fin n → kˣ →* ℂˣ := fun i => ω i * absPow k (((n : ℂ) - 1) / 2) with hψd
  have hval : ∀ w : Equiv.Perm (Fin n), (∀ j, c j * (torusChar (ψ ∘ w) (t j) : ℂ) = μ j) →
      ∀ i, ω (w i) (unif k) = α i := fun w h i => by
    refine Units.ext (mul_right_cancel₀ (inv_ne_zero (pow_ne_zero (i : ℕ) hq))
      (OrdinaryOrderOne.eq_of_prod (a := fun i => (ω (w i) (unif k) : ℂ) * ((Nat.card 𝓀[k] : ℂ) ^ (i : ℕ))⁻¹) hα0 (fun j => ?_) i))
    have h1 := OrdB.num (fun i => ω (w i)) (j := j + 1) j.2
    rw [← mul_assoc] at h1
    rw [← hμ, ← h j]
    refine Eq.trans ?_ h1.symm
    simp only [psEig, Nat.lt_succ_iff, Fin.val_fin_le]
  have huniq : ∀ w w' : Equiv.Perm (Fin n), (∀ j, c j * (torusChar (ψ ∘ w) (t j) : ℂ) = μ j) →
      (∀ j, c j * (torusChar (ψ ∘ w') (t j) : ℂ) = μ j) → w = w' := fun w w' h h' => by
    refine Equiv.ext fun i => ?_
    have h1 := hval w h (w.symm (w' i))
    rw [Equiv.apply_symm_apply, hval w' h' i] at h1
    conv_lhs => rw [hα h1, Equiv.apply_symm_apply]
  have hχ : ∀ χ : (Fin n → kˣ) →* ℂˣ, ∀ y ∈ E, y ≠ 0 → (∀ s, jacB π s y = (χ s : ℂ) • y) →
      (∀ j, c j * (χ (t j) : ℂ) = μ j) ∧ ∃ w : Equiv.Perm (Fin n), χ = torusChar (ψ ∘ w) := fun χ y hy hy0 hχ => by
    refine ⟨fun j => OrdB.eq_of_gen ?_ hy0 ((Submodule.mem_iInf _).1 hy j), ?_⟩
    · rw [LinearMap.smul_apply, hχ, smul_smul]
    have h1 : (⨅ t, Module.End.maxGenEigenspace (jacB π t) (χ t : ℂ) : Submodule ℂ _) ≠ ⊥ :=
      (Submodule.ne_bot_iff _).2 ⟨y, (Submodule.mem_iInf _).2 fun t =>
        (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by rw [OrdB.pow_eig (hχ t)]; simp⟩, hy0⟩
    have h2 := (Nat.pos_of_ne_zero fun h => h1 (Submodule.finrank_eq_zero.1 h)).trans_le (hmult χ)
    obtain ⟨⟨w, hw⟩⟩ := (Nat.card_pos_iff.1 h2).1
    exact ⟨w, hw⟩
  obtain ⟨χ, y, hy, hy0, hχy⟩ := OrdB.exists_eig (jacB π) E
    ((Submodule.ne_bot_iff _).2 ⟨_, hpE x hx, fun h => hx0 (hinj x hx h)⟩) hEs
  obtain ⟨h0, w, rfl⟩ := hχ χ y hy hy0 hχy
  have hgen : E ≤ ⨅ s, Module.End.maxGenEigenspace (jacB π s) (torusChar (ψ ∘ w) s : ℂ) := by
    refine le_iInf (OrdB.le_gen _ E hEs _ fun χ y hy hy0 h => ?_)
    obtain ⟨h1, w', rfl⟩ := hχ χ y hy hy0 h
    rw [huniq w w' h0 h1]
  have hE1 : Module.finrank ℂ E ≤ 1 := by
    refine (Submodule.finrank_mono hgen).trans ((hmult _).trans ?_)
    have key : ∀ a : {w' : Equiv.Perm (Fin n) // torusChar (ψ ∘ w) = torusChar (ψ ∘ w')}, w = a.1 := fun a =>
      huniq _ _ h0 (a.2 ▸ h0)
    exact Finite.card_le_one_iff_subsingleton.2 ⟨fun a b => Subtype.ext ((key a).symm.trans (key b))⟩
  refine (LinearMap.rank_le_of_injective (p.restrict hpE) ?_).trans ?_
  · exact (injective_iff_map_eq_zero _).2 fun v h => Subtype.ext (hinj v v.2 (congrArg Subtype.val h))
  · rw [← Module.finrank_eq_rank]
    exact_mod_cast hE1
end
