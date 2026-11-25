module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.IsClosedUnipRad

@[expose] public section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.JacquetKernel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : ℕ} (G : Grp k n)

theorem mem_NO {g : GL (Fin n) k} : g ∈ G.NO ↔ g ∈ unipRad k G.e ∧ g ∈ KO k (Fin n) := Iff.rfl

theorem zEl_eq_dia (ϖ : kˣ) :
    G.zEl ϖ = GlobalTheory.DepthZeroJac.dia G.e ϖ.ne_zero (fun a => G.s - 1 - (a : ℕ)) := by
  apply Units.ext
  rw [GlobalTheory.DepthZeroJac.dia_val]
  ext i j
  obtain ⟨⟨a, i'⟩, rfl⟩ := G.e.surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := G.e.surjective j
  by_cases hab : a = b
  · subst hab
    rw [zEl, leviEmb_apply_same]
    by_cases hij : i' = j'
    · subst hij
      simp [Matrix.scalar_apply, Matrix.diagonal_pow]
    · have hne : G.e ⟨a, i'⟩ ≠ G.e ⟨a, j'⟩ := fun h => hij (by simpa using h)
      simp [Matrix.scalar_apply, Matrix.diagonal_pow, Matrix.diagonal_apply_ne _ hij, hne]
  · rw [zEl, leviEmb_apply_ne _ _ _ hab, Matrix.diagonal_apply_ne]
    intro h
    exact hab (congrArg Sigma.fst (G.e.injective h))

theorem zEl_pow (ϖ : kˣ) (m : ℕ) :
    G.zEl ϖ ^ m = GlobalTheory.DepthZeroJac.dia G.e ϖ.ne_zero (fun a => m * (G.s - 1 - (a : ℕ))) := by
  induction m with
  | zero =>
    rw [pow_zero]
    simp only [zero_mul]
    exact (GlobalTheory.DepthZeroJac.dia_zero G.e ϖ.ne_zero).symm
  | succ m ih =>
    rw [pow_succ, ih, zEl_eq_dia, ← GlobalTheory.DepthZeroJac.dia_add]
    congr 1
    funext a
    show m * (G.s - 1 - (a : ℕ)) + (G.s - 1 - (a : ℕ)) = (m + 1) * (G.s - 1 - (a : ℕ))
    ring

theorem deep_unif {ϖ : kˣ} (h : IsUnif ϖ) : GlobalTheory.IwahoriInj.Deep 1 (ϖ : k) := by
  obtain ⟨w, hw, hwϖ⟩ := h
  rw [GlobalTheory.IwahoriInj.deep_one_iff, ← hwϖ]
  have hnu : ¬ IsUnit w := hw.not_isUnit
  exact (Valuation.Integer.not_isUnit_iff_valuation_lt_one (v := valuation k) (x := w)).1 hnu

theorem intM_of_deep {g : Matrix (Fin n) (Fin n) k} (h : ∀ i j, GlobalTheory.IwahoriInj.Deep 0 ((g - 1) i j)) :
    GlobalTheory.StepData.IntM g := by
  have e : g = (g - 1) + 1 := by abel
  rw [e]
  exact GlobalTheory.StepData.IntM.add (fun i j => GlobalTheory.DepthZeroJac.mem_int_of_deep (h i j))
    (GlobalTheory.StepData.intM_one (k := k) (n := Fin n))

theorem eventually_conj_deep {c : k} (hc : c ≠ 0) (hc1 : GlobalTheory.IwahoriInj.Deep 1 c) {u : GL (Fin n) k}
    (hu : u ∈ unipRad k G.e) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ i j, GlobalTheory.IwahoriInj.Deep 0
      (((GlobalTheory.DepthZeroJac.dia G.e hc (fun a => m * (G.s - 1 - (a : ℕ))) * u *
        (GlobalTheory.DepthZeroJac.dia G.e hc (fun a => m * (G.s - 1 - (a : ℕ))))⁻¹).val - 1) i j) := by
  have key : ∀ᶠ M : ℕ in Filter.atTop, ∀ i j, GlobalTheory.IwahoriInj.Deep (-(M : ℤ)) ((u.val - 1) i j) := by
    simp only [Filter.eventually_all]
    exact fun i j => GlobalTheory.IwahoriInj.eventually_deep _
  filter_upwards [key] with m hm
  intro i j
  rw [GlobalTheory.DepthZeroJac.conj_sub_apply]
  try dsimp only
  by_cases h : blk G.e i < blk G.e j
  · have h1 : ((blk G.e i : Fin G.s) : ℕ) < (blk G.e j : Fin G.s) := h
    have h2 : ((blk G.e j : Fin G.s) : ℕ) < G.s := (blk G.e j).2
    obtain ⟨t, ht⟩ : ∃ t, m * (G.s - 1 - ((blk G.e i : Fin G.s) : ℕ)) =
        m * (G.s - 1 - ((blk G.e j : Fin G.s) : ℕ)) + m + t := by
      refine Nat.exists_eq_add_of_le ?_
      calc m * (G.s - 1 - ((blk G.e j : Fin G.s) : ℕ)) + m
          = m * (G.s - 1 - ((blk G.e j : Fin G.s) : ℕ) + 1) := by ring
        _ ≤ m * (G.s - 1 - ((blk G.e i : Fin G.s) : ℕ)) := Nat.mul_le_mul_left _ (by omega)
    have e1 : ∀ (A : ℕ) (x : k), c ^ (A + m + t) * x * (c ^ A)⁻¹ = c ^ m * c ^ t * x := by
      intro A x
      have hA : c ^ A ≠ 0 := pow_ne_zero _ hc
      rw [pow_add, pow_add]
      calc c ^ A * c ^ m * c ^ t * x * (c ^ A)⁻¹ = (c ^ A * (c ^ A)⁻¹) * (c ^ m * c ^ t * x) := by ring
        _ = c ^ m * c ^ t * x := by rw [mul_inv_cancel₀ hA, one_mul]
    rw [ht, e1]
    have d1 : GlobalTheory.IwahoriInj.Deep ((m : ℤ) * 1) (c ^ m) := GlobalTheory.DepthZeroJac.deep_pow hc1 m
    have d2 : GlobalTheory.IwahoriInj.Deep ((t : ℤ) * 1) (c ^ t) := GlobalTheory.DepthZeroJac.deep_pow hc1 t
    exact ((d1.mul d2).mul (hm i j)).mono (by omega)
  · rw [GlobalTheory.DepthZeroJac.sub_one_of_mem_unipRad hu h, mul_zero, zero_mul]
    exact GlobalTheory.IwahoriInj.deep_zero 0

theorem mem_NO_of_deep {D u : GL (Fin n) k} (hun : D * u * D⁻¹ ∈ unipRad k G.e)
    (h1 : ∀ i j, GlobalTheory.IwahoriInj.Deep 0 (((D * u * D⁻¹).val - 1) i j))
    (h2 : ∀ i j, GlobalTheory.IwahoriInj.Deep 0 (((D * u⁻¹ * D⁻¹).val - 1) i j)) : D * u * D⁻¹ ∈ G.NO := by
  refine (mem_NO G).2 ⟨hun, ?_⟩
  rw [GlobalTheory.StepData.mem_KO]
  have hinv : (D * u * D⁻¹)⁻¹ = D * u⁻¹ * D⁻¹ := by group
  exact ⟨intM_of_deep h1, by rw [hinv]; exact intM_of_deep h2⟩

theorem eventually_conj_mem_NO {ϖ : kˣ} (hϖ : IsUnif ϖ) {u : GL (Fin n) k} (hu : u ∈ unipRad k G.e) :
    ∀ᶠ m : ℕ in Filter.atTop, G.zEl ϖ ^ m * u * (G.zEl ϖ ^ m)⁻¹ ∈ G.NO := by
  have hc1 := deep_unif hϖ
  filter_upwards [eventually_conj_deep G ϖ.ne_zero hc1 hu,
    eventually_conj_deep G ϖ.ne_zero hc1 (inv_mem hu)] with m h1 h2
  rw [zEl_pow]
  refine mem_NO_of_deep G ?_ h1 h2
  refine GlobalTheory.DepthZeroJac.mem_unipRad_of fun i j h => ?_
  rw [GlobalTheory.DepthZeroJac.conj_sub_apply, GlobalTheory.DepthZeroJac.sub_one_of_mem_unipRad hu h, mul_zero, zero_mul]

theorem eventually_mem_twKer_NO {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) {ϖ : kˣ} (hϖ : IsUnif ϖ) {x : V}
    (hx : x ∈ twKer π (unipRad k G.e) 1) :
    ∀ᶠ m : ℕ in Filter.atTop, π (G.zEl ϖ ^ m) x ∈ twKer π G.NO 1 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, w, rfl⟩ := hy
    filter_upwards [eventually_conj_mem_NO G hϖ u.2] with m hm
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
    have e : π (G.zEl ϖ ^ m) (π (u : GL (Fin n) k) w) =
        π (G.zEl ϖ ^ m * (u : GL (Fin n) k) * (G.zEl ϖ ^ m)⁻¹) (π (G.zEl ϖ ^ m) w) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    rw [e]
    exact Submodule.subset_span ⟨⟨_, hm⟩, π (G.zEl ϖ ^ m) w, by simp⟩
  | zero => simp
  | add y z _ _ hy hz =>
    filter_upwards [hy, hz] with m h1 h2
    rw [map_add (f := _)]
    exact add_mem h1 h2
  | smul a y _ hy =>
    filter_upwards [hy] with m h1
    rw [map_smul]
    exact Submodule.smul_mem _ a h1

theorem isClosed_zero : IsClosed ({0} : Set k) := isClosed_singleton

theorem isOpen_KO : IsOpen (KO k (Fin n) : Set (GL (Fin n) k)) :=
  Subgroup.isOpen_mono GlobalTheory.StepData.KOne_le_KO GlobalTheory.StepData.isOpen_KOne

end UpperTheory.TNZ.Grp.JacquetKernel

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : ℕ}

theorem step_jacKer (G : Grp k n) : G.JacquetKernelProp := by
  intro _ _ _ _ _ _ _ _ _ hU ϖ hϖ V _ _ π hπ x hx h0
  have h1 : x ∈ twKer π (unipRad k G.e) 1 := (Submodule.Quotient.mk_eq_zero _).1 h0
  obtain ⟨m, hm⟩ := (JacquetKernel.eventually_mem_twKer_NO G π hϖ h1).exists
  refine ⟨m, ?_⟩
  have hc : IsCompact (G.NO : Set (GL (Fin n) k)) := P_TzE.isCompact_NO G
  have : Finite (↥G.NO ⧸ G.zN ϖ m) := P_TzE.finite_quot G ϖ m
  let : Fintype (↥G.NO ⧸ G.zN ϖ m) := Fintype.ofFinite _
  have hfix : ∀ u ∈ G.zN ϖ m,
      π ((u : ↥G.NO) : GL (Fin n) k) (π (G.zEl ϖ ^ m) x) = π (G.zEl ϖ ^ m) x := by
    intro u hu
    rw [zN, Subgroup.mem_subgroupOf] at hu
    obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.1 hu
    rw [← hyu]
    change π (G.zEl ϖ ^ m * y * (G.zEl ϖ ^ m)⁻¹) (π (G.zEl ϖ ^ m) x) = π (G.zEl ϖ ^ m) x
    have hyx : π y x = x := by
      rw [hx y (hU.1 y hy).1, (hU.1 y hy).2, one_smul]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, hyx]
  have hid := GlobalTheory.LocGL.idem_eq_cosetSum hπ hc (G.zN ϖ m) hfix
  rw [(GlobalTheory.LocGL.idem_eq_zero_iff hπ hc).2 hm] at hid
  have hcard : ((Fintype.card (↥G.NO ⧸ G.zN ϖ m) : ℂ))⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  have hsum := (smul_eq_zero.1 hid.symm).resolve_left hcard
  show (∑ᶠ c : ↥G.NO ⧸ G.zN ϖ m, π ((Quotient.out c : ↥G.NO) : GL (Fin n) k) (π (G.zEl ϖ ^ m) x)) = 0
  rw [finsum_eq_sum_of_fintype]
  exact hsum

end UpperTheory.TNZ.Grp
