import Mathlib

variable {G A B α : Type*} [Group G] [MulAction G α]

class DoublyTransitive (G α : Type*) [Group G] [MulAction G α] where
  exists_smul_both_eq : ∀ a b x y : α, a ≠ b → x ≠ y → ∃ g : G, g • a = x ∧ g • b = y

namespace DoublyTransitive

theorem stabilizer_maximal [DoublyTransitive G α] (H : Subgroup G) (a : α) :
    MulAction.stabilizer G a ≤ H → H = ⊤ ∨ H = MulAction.stabilizer G a := by
  let S := MulAction.stabilizer G a
  have (g : G) : ∀ x : G, x ∉ S → (g ∈ S ∨ ∃ (h i : S), g = h * x * i) := by
    intro g' hg'
    by_cases hg : g ∈ S
    · exact Or.inl hg
    · have g'_nonstab : g' • a ≠ a := by
        intro ga'
        apply hg'
        apply MulAction.mem_stabilizer_iff.mpr
        nth_rw 2 [← ga']
      have g_nonstab : g • a ≠ a := by
        intro ga
        apply hg
        apply MulAction.mem_stabilizer_iff.mpr
        nth_rw 2 [← ga]
      obtain ⟨y, hy⟩ :=
        @exists_smul_both_eq G α _ _ _ (g • a) a (g' • a) a g_nonstab g'_nonstab
      have y_mem : y ∈ S := MulAction.mem_stabilizer_iff.mpr hy.2
      have y_inv_mem : y⁻¹ ∈ S := (Subgroup.inv_mem_iff S).mpr y_mem
      have i_mem : g'⁻¹ * y * g ∈ S := by
        apply MulAction.mem_stabilizer_iff.mpr
        rw [mul_smul, mul_smul, hy.left, ← mul_smul, inv_mul_cancel, one_smul]
      right
      use ⟨y⁻¹, y_inv_mem⟩
      use ⟨g'⁻¹ * y * g, i_mem⟩
      simp only
      group
  intro hH
  by_cases hHleS : H ≤ S
  · right
    apply le_antisymm hHleS hH
  · left
    rcases Set.not_subset.mp hHleS with ⟨x, hx⟩
    apply le_antisymm (by exact Subgroup.toSubmonoid_le.mp fun ⦃x⦄ a ↦ trivial)
    intro g hg
    cases this g x hx.right with
    | inl h1 => exact hH h1
    | inr h2 =>
      rcases h2 with ⟨h, i, hhi⟩
      rw [hhi]
      refine (Subgroup.mul_mem_cancel_right H ?_).mpr ?_
      · apply hH (SetLike.coe_mem i)
      · refine (Subgroup.mul_mem_cancel_right H hx.left).mpr ?_
        apply hH (SetLike.coe_mem h)

theorem normal_trivial_or_transitive
    [DoublyTransitive G α] (N : Subgroup G) (N_normal : N.Normal) :
    (∀ n : N, ∀ a : α, n • a = a) ∨ (∀ a b : α, ∃ n : N, n • a = b) := by
  by_cases h_triv : (∀ n : N, ∀ a : α, n • a = a)
  · exact (Or.inl h_triv)
  · simp only [not_forall] at h_triv
    rcases h_triv with ⟨n, x, hx⟩
    right
    intro a b
    by_cases beqa : b = a
    · use 1; rw [one_smul, beqa]
    · obtain ⟨g, hg⟩ :=
        @exists_smul_both_eq G α _ _ _ (n • x) x b a hx (beqa)
      have : g * n * g⁻¹ ∈ N := Subgroup.Normal.conj_mem N_normal ↑n (SetLike.coe_mem n) g
      use ⟨g * n * g⁻¹, this⟩
      simp only [Subgroup.mk_smul]
      rw [← hg.right, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one, ← hg.left, mul_smul]
      exact (smul_left_cancel_iff g).mpr rfl

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem fixing_top_normal : (fixingSubgroup G (⊤ : Set α)).Normal := by
  refine { conj_mem := ?_ }
  intro _ n_fix _ _
  rw [mem_fixingSubgroup_iff] at n_fix
  rw [mul_smul, mul_smul, n_fix, ← mul_smul, mul_inv_cancel, one_smul]
  exact Set.mem_preimage.mp trivial

structure Iwasawa (G α : Type*) [Group G] [MulAction G α] [DoublyTransitive G α] where
  non_trivial : Nontrivial G
  commutator_all : ⊤ = commutator G
  x : α
  stab_sub : Subgroup (MulAction.stabilizer G x)
  stab_sub_normal : stab_sub.Normal
  stab_sub_comm : IsMulCommutative stab_sub
  stab_sub_gen : ∀ x : G, ∃ s : stab_sub, ∃ g : G, x = g * s * g⁻¹

variable {G A B α : Type*} [Group G] [MulAction G α] [DoublyTransitive G α]

theorem QuotientGroup_isSimple_iff (N : Subgroup G) [N.Normal] :
  (∀ (H : Subgroup G), H.Normal → H ≥ N → H ≤ N ∨ ⊤ ≤ H) ↔ IsSimpleGroup (G ⧸ N) := sorry

theorem iwasawa_simple (h : Iwasawa G α) [(fixingSubgroup G (⊤ : Set α)).Normal]
    : IsSimpleGroup (G ⧸ (fixingSubgroup G (⊤ : Set α))) := by
  rw [← QuotientGroup_isSimple_iff]
  intro N N_Normal
  let H := (MulAction.stabilizer G h.x)
  cases stabilizer_maximal (N ⊔ H) h.x (le_sup_right) with
  | inr HN_eq_stab =>
    intro hN
    left
    intro n nN
    cases @normal_trivial_or_transitive G α _ _ _ N N_Normal with
    | inr n_trans =>
      apply (mem_fixingSubgroup_iff G).mpr
      intro y _
      rcases n_trans h.x y with ⟨m, hm⟩
      have m_stab : m • h.x = h.x := sorry
      rcases n_trans h.x (n • y) with ⟨o, ho⟩
      have o_stab : o • h.x = h.x := sorry
      rw [← ho, o_stab, ← m_stab, hm]
    | inl H_triv =>
      apply (mem_fixingSubgroup_iff G).mpr
      intro y _
      exact H_triv ⟨n, nN⟩ y
  | inl HN_eq_all =>
    intro hN
    right
    let U : Subgroup G := h.stab_sub.map H.subtype
    have NUNorm : (N ⊔ U).Normal := sorry
    have NHeq : N ⊔ H = (N ⊔ U) := by
      sorry
    have : IsMulCommutative U := by sorry
    rw [NHeq] at HN_eq_all
    rw [h.commutator_all]
    apply Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
    rw [← HN_eq_all]
    exact this
