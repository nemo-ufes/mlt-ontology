import MLTStar

/-!
# Experiment: where subordination becomes irreflexive

`INSIGHTS.md` §5 records that `IsSubordinateTo t t` is not refutable, and
guesses that restricting to *ordered* types would fix it. That guess is wrong,
and this file says what the right condition is instead.

Self-subordination says every instance of `t` proper specializes another
instance of `t`. Unfolded, that is precisely the statement that the instances of
`t` have **no maximal element** under proper specialization. So irreflexivity is
an *ascending* chain condition, and `a4` — which constrains instantiation
*descending* — is simply the wrong tool. Being ordered does not supply an
ascending condition either, which is why the guess fails.

What is true is the finiteness bound: a self-subordinate type generates a
strictly ascending chain of its own instances, so `Nat` embeds into the domain.
Every finite model therefore has irreflexive subordination, and any
counterexample must be infinite.
-/

namespace MLTStar.Subordination

universe u
variable {E : Type u} [Domain E]

/-! ## Self-subordination is exactly the failure of maximality -/

/-- `t` is subordinate to itself exactly when it is a type whose instances have
no maximal element under proper specialization. This is unfolding, but it is the
unfolding that matters: the condition is about ascending chains. -/
theorem isSubordinateTo_self_iff {t : E} :
    IsSubordinateTo t t ↔
      IsType t ∧ ∀ s, iof s t → ∃ s', iof s' t ∧ ProperSpecializes s s' :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1, h.2⟩⟩

/-- A maximal instance refutes self-subordination. -/
theorem not_isSubordinateTo_self_of_maximal {t m : E}
    (hm : iof m t) (hmax : ∀ s, iof s t → ¬ ProperSpecializes m s) :
    ¬ IsSubordinateTo t t := by
  intro h
  obtain ⟨s, hs, hps⟩ := h.2.2 m hm
  exact hmax s hs hps

/-! ## Self-subordination forces an infinite domain

The witnesses chain: each instance proper specializes a further instance, and
proper specialization is transitive and irreflexive, so the chain never repeats.
-/

variable {t : E} (h : IsSubordinateTo t t)

/-- One step along the chain of instances. -/
noncomputable def step (x : {x : E // iof x t}) : {x : E // iof x t} :=
  ⟨(h.2.2 x.1 x.2).choose, (h.2.2 x.1 x.2).choose_spec.1⟩

theorem step_spec (x : {x : E // iof x t}) :
    ProperSpecializes x.1 (step h x).1 :=
  (h.2.2 x.1 x.2).choose_spec.2

noncomputable def chainAux (x₀ : {x : E // iof x t}) : Nat → {x : E // iof x t}
  | 0 => x₀
  | n + 1 => step h (chainAux x₀ n)

/-- A strictly ascending chain of instances of `t`. -/
noncomputable def chain (x₀ : {x : E // iof x t}) (n : Nat) : E := (chainAux h x₀ n).1

theorem chain_iof (x₀ : {x : E // iof x t}) (n : Nat) : iof (chain h x₀ n) t :=
  (chainAux h x₀ n).2

theorem chain_lt [Extensional E] (x₀ : {x : E // iof x t}) :
    ∀ m n, m < n → ProperSpecializes (chain h x₀ m) (chain h x₀ n) := by
  intro m n hmn
  induction n with
  | zero => exact absurd hmn (by omega)
  | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with hlt | heq
      · exact (ih hlt).trans (step_spec h (chainAux h x₀ k))
      · subst heq; exact step_spec h (chainAux h x₀ m)

theorem chain_injective [Extensional E] (x₀ : {x : E // iof x t}) :
    ∀ m n, chain h x₀ m = chain h x₀ n → m = n := by
  intro m n heq
  rcases Nat.lt_trichotomy m n with hlt | rfl | hgt
  · exact absurd heq (chain_lt h x₀ m n hlt).2
  · rfl
  · exact absurd heq.symm (chain_lt h x₀ n m hgt).2

include h in
/-- A type subordinate to itself embeds `Nat` into its own instances. So no
finite model has one. -/
theorem nat_embeds_of_self_subordinate [Extensional E] :
    ∃ f : Nat → E, (∀ n, iof (f n) t) ∧ ∀ m n, f m = f n → m = n := by
  obtain ⟨x₀, hx₀⟩ := h.1
  exact ⟨chain h ⟨x₀, hx₀⟩, chain_iof h ⟨x₀, hx₀⟩, chain_injective h ⟨x₀, hx₀⟩⟩

end MLTStar.Subordination

/-! ## In the four-element model, subordination is irreflexive

Not because its types are ordered — because it is finite. -/

namespace MLTStar.Model

instance instDecidableIsSubordinateTo (a b : W) : Decidable (IsSubordinateTo a b) :=
  inferInstanceAs (Decidable (IsType a ∧ IsType b ∧
    ∀ t₃, iof t₃ a → ∃ t₄, iof t₄ b ∧ ProperSpecializes t₃ t₄))

theorem not_isSubordinateTo_self : ∀ t : W, ¬ IsSubordinateTo t t := by decide

/-- Indeed the model has no subordination at all. -/
theorem no_subordination : ∀ a b : W, ¬ IsSubordinateTo a b := by decide

end MLTStar.Model
