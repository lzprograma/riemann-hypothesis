module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem Generated.proof (hE : Extension.Statement.{u, w, w}) : Generated.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x Q
  obtain ⟨M, hMgam, hMtilde⟩ := hE S Ω N x Ω Q.toSubFamily Q.fg
  obtain ⟨n, deg, gen, hgen, hM⟩ := M.fg
  refine ⟨∑ j, |deg j|, fun c hc I => le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro z hz
    exact (Submodule.mem_iInf _).mp hz I
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  set T := Submodule.span (chartRing S x I) ((Q.twist (twistSys S x c)).secs : Set Ω) with hT

  have hgenT : ∀ (j : Fin n) (f s : Poly S N) (e e' : ℕ), s ∈ monos I.1 → f.IsHomogeneous e' →
      s.IsHomogeneous e → (e' : ℤ) + deg j = e →
      x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j)) ∈ T := by
    intro j f s e e' hs hf hse hee
    have hd : deg j ≤ c := (le_abs_self (deg j)).trans
      ((Finset.single_le_sum (fun j _ => abs_nonneg (deg j)) (Finset.mem_univ j)).trans hc)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = c - deg j := ⟨(c - deg j).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hsec : x i ^ k * gen j ∈ (Q.twist (twistSys S x c)).secs := by
      have h1 := M.smul_mem k (deg j) (X i ^ k) (gen j) (isHomogeneous_X_pow i k) (hgen j)
      have h2 : deg j + (k : ℤ) = c := by omega
      rw [h2] at h1
      have h3 := hMgam c h1
      rwa [map_pow, aeval_X, smul_eq_mul] at h3
    have hα : aeval x f / aeval x s ∈ twistMod S x (-deg j) I :=
      Submodule.subset_span ⟨f, s, e, e', hs, hf, hse, by omega, rfl⟩
    rw [twistMod_eq_span (-deg j) I hi, Submodule.mem_span_singleton] at hα
    obtain ⟨b, hb⟩ := hα
    rw [chartRing_smul_def] at hb
    have e1 : x i ^ c * x i ^ (-deg j) = x i ^ k := by
      rw [← zpow_add₀ hxi, ← zpow_natCast, hk]
      congr 1
    have e2 : x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j)) = b • (x i ^ k * gen j) := by
      rw [chartRing_smul_def, ← e1]
      calc x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j))
          = x i ^ c * (aeval x f / aeval x s) * gen j := by ring
        _ = x i ^ c * ((b : Ω) * x i ^ (-deg j)) * gen j := by rw [hb]
        _ = (b : Ω) * (x i ^ c * x i ^ (-deg j) * gen j) := by ring
    rw [e2]
    exact T.smul_mem b (Submodule.subset_span hsec)

  let φ : Ω →ₗ[chartRing S x I] Ω :=
    { toFun := (x i ^ c * ·), map_add' := mul_add _
      map_smul' := fun b y => by simp only [RingHom.id_apply, chartRing_smul_def]; ring }
  let TS : Submodule S Ω :=
    { carrier := T, add_mem' := T.add_mem, zero_mem' := T.zero_mem
      smul_mem' := fun r z h => by
        have e : r • z = algebraMap S (chartRing S x I) r • z := by
          rw [Algebra.smul_def, chartRing_smul_def]; rfl
        rw [SetLike.mem_coe, e]; exact T.smul_mem _ h }
  have key : ∀ y ∈ M.tilde 0 I, x i ^ c * y ∈ T := by
    intro y hy
    change y ∈ Submodule.span _ _ at hy
    refine (Submodule.span_le.mpr ?_ : _ ≤ T.comap φ) hy
    rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    let ψ : Ω →ₗ[S] Ω :=
      { toFun := fun m => x i ^ c * ((aeval x s)⁻¹ • m)
        map_add' := fun _ _ => by rw [smul_add, mul_add]
        map_smul' := fun r m => by
          simp only [RingHom.id_apply, smul_eq_mul, Algebra.smul_def]; ring }
    refine (Submodule.span_le.mpr ?_ : _ ≤ TS.comap ψ) (hM a hm)
    rintro _ ⟨j, f, e', hf, hee, rfl⟩
    change x i ^ c * ((aeval x s)⁻¹ • _) ∈ T
    rw [smul_eq_mul, smul_eq_mul]
    exact hgenT j f s e e' hs hf hse (by omega)
  change Submodule.span _ _ ≤ T
  rw [Submodule.span_le]
  rintro _ ⟨q, hq, y, hy, rfl⟩
  change q ∈ twistMod S x c I at hq
  rw [twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
  obtain ⟨a, rfl⟩ := hq
  have hy' : y ∈ M.tilde 0 I := by rw [hMtilde I]; exact hy
  have : (a • x i ^ c) • y = a • (x i ^ c * y) := by
    rw [smul_eq_mul, chartRing_smul_def, chartRing_smul_def, mul_assoc]
  rw [SetLike.mem_coe, this]
  exact T.smul_mem a (key y hy')

end

end GroundTheory.Heights₂.Heights.Kleiman
