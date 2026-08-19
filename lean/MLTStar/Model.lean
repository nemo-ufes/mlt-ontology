import MLTStar.Stratification

/-!
# A model of MLT*, and hence a consistency proof

The Alloy specifications in this repository establish consistency by finding
instances within a bounded scope; the TPTP file records a `satisfiability`
report from an external prover.  This module does better: it exhibits an
explicit four-element model, verified by the Lean kernel.

The model is the smallest one there is.  `Constants` forces at least one
individual to exist (`MLTStar.exists_individual`), and that individual forces
the chain `cIndividual : cFot : cSot`, all four of which are distinct.

```
    ind  :  cInd  :  cFot  :  cSot
```

(`a : b` reads "`a` is an instance of `b`"; these are the only instantiations.)

Because the axioms are consistent, none of them is vacuous, and in particular
the strengthened, higher-order form of `a4` used in `MLTStar.Grounded.grounded` —
which quantifies over *all* classes of types rather than only the finite sets
that TPTP's auxiliary set theory forces to exist — is not contradictory.

The model is also small enough to be a useful sanity check on the definitions:
`MLTStar.Model.checks` below evaluates a batch of MLT* predicates in it by
kernel computation.
-/

namespace MLTStar
namespace Model

/-- The four entities of the minimal model. -/
inductive W where
  /-- The one individual. -/
  | ind
  /-- The type of individuals. -/
  | cInd
  /-- The type of first-order types. -/
  | cFot
  /-- The type of second-order types. -/
  | cSot
  deriving DecidableEq, Repr

/-- Instantiation in the model: a single chain `ind : cInd : cFot : cSot`. -/
def wiof (a b : W) : Prop :=
  (a = .ind ∧ b = .cInd) ∨ (a = .cInd ∧ b = .cFot) ∨ (a = .cFot ∧ b = .cSot)

instance : Domain W := ⟨wiof⟩

instance instDecidableWiof (a b : W) : Decidable (wiof a b) := by
  unfold wiof; infer_instance

instance instDecidableIof (a b : W) : Decidable (iof a b) :=
  inferInstanceAs (Decidable (wiof a b))

/-! ## Decidability

`W` is finite, so every quantifier over it can be evaluated.  Supplying these
instances lets the kernel check the axioms of `MLTStar.Extensional`/`MLTStar.Grounded` and
`MLTStar.Constants` by computation, apart from `grounded`, which quantifies over
arbitrary classes and is proved by hand below. -/

instance instDecidableForallW (p : W → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .ind ∧ p .cInd ∧ p .cFot ∧ p .cSot)
    ⟨fun h x => by cases x <;> simp_all, fun h => ⟨h _, h _, h _, h _⟩⟩

instance instDecidableExistsW (p : W → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p .ind ∨ p .cInd ∨ p .cFot ∨ p .cSot)
    ⟨fun h => by rcases h with h | h | h | h <;> exact ⟨_, h⟩,
     fun ⟨x, hx⟩ => by cases x <;> simp_all⟩

instance instDecidableIsType (x : W) : Decidable (IsType x) :=
  inferInstanceAs (Decidable (∃ y, iof y x))

instance instDecidableIndividual (x : W) : Decidable (Individual x) :=
  inferInstanceAs (Decidable (¬ ∃ y, iof y x))

instance instDecidableFirstOrderType (x : W) : Decidable (FirstOrderType x) :=
  inferInstanceAs (Decidable (IsType x ∧ ∀ y, iof y x → Individual y))

instance instDecidableSecondOrderType (x : W) : Decidable (SecondOrderType x) :=
  inferInstanceAs (Decidable (IsType x ∧ ∀ y, iof y x → FirstOrderType y))

instance instDecidableSpecializes (a b : W) : Decidable (Specializes a b) :=
  inferInstanceAs (Decidable (IsType a ∧ ∀ e, iof e a → iof e b))

instance instDecidableProperSpecializes (a b : W) : Decidable (ProperSpecializes a b) :=
  inferInstanceAs (Decidable (Specializes a b ∧ a ≠ b))

instance instDecidableIsPowertypeOf (a b : W) : Decidable (IsPowertypeOf a b) :=
  inferInstanceAs (Decidable (IsType a ∧ ∀ t, iof t a ↔ Specializes t b))

/-! ## The axioms hold -/

theorem not_isType_ind : ¬ IsType W.ind := by decide

/-- `a4` in the model: any non-empty class of types contains a member with an
instance outside the class.  Take the least member of the chain that is in the
class; its instance is the next entity down, which is not in the class — for
`cInd` because `ind` is not a type, and otherwise by the case assumption. -/
theorem grounded (S : W → Prop) (hne : ∃ y, S y) (hty : ∀ y, S y → IsType y) :
    ∃ y, S y ∧ ∃ z, iof z y ∧ ¬ S z := by
  by_cases h₁ : S .cInd
  · exact ⟨.cInd, h₁, .ind, by decide, fun h => not_isType_ind (hty _ h)⟩
  · by_cases h₂ : S .cFot
    · exact ⟨.cFot, h₂, .cInd, by decide, h₁⟩
    · by_cases h₃ : S .cSot
      · exact ⟨.cSot, h₃, .cFot, by decide, h₂⟩
      · obtain ⟨y, hy⟩ := hne
        cases y
        · exact absurd (hty _ hy) not_isType_ind
        · exact absurd hy h₁
        · exact absurd hy h₂
        · exact absurd hy h₃

instance : Extensional W where
  typeExtensionality := by decide

instance : Grounded W where
  grounded := grounded

instance : Constants W where
  cIndividual := .cInd
  cFot := .cFot
  cSot := .cSot
  cIndividual_spec := by decide
  cFot_spec := by decide
  cSot_spec := by decide

/-! ## Consistency

Every theorem of the development therefore holds of something.  Read the other
way: the axioms of `MLTStar.Extensional`/`MLTStar.Grounded` together with `MLTStar.Constants` have a
model, so they cannot prove `False`. -/

/-- MLT* is consistent: a domain satisfying all of its axioms exists. -/
theorem consistent :
    ∃ (E : Type) (_ : Domain E) (_ : Extensional E) (_ : Grounded E), Nonempty (Constants E) :=
  ⟨W, inferInstance, inferInstance, inferInstance, ⟨inferInstance⟩⟩

/-! ## The model computed

A batch of MLT* predicates, evaluated in the model by the kernel.  These are
not needed for anything above; they are a check that the definitions say what
they are meant to say. -/

theorem checks :
    -- individuals and types
    Individual W.ind ∧ IsType W.cInd ∧ IsType W.cFot ∧ IsType W.cSot ∧
    -- the orders
    FirstOrderType W.cInd ∧ ¬ FirstOrderType W.cFot ∧
    SecondOrderType W.cFot ∧ ¬ SecondOrderType W.cSot ∧
    -- the constants are Cardelli powertypes of one another
    IsPowertypeOf W.cFot W.cInd ∧ IsPowertypeOf W.cSot W.cFot ∧
    -- nothing specializes anything else, so the model has no subtyping
    (∀ a b : W, Specializes a b → a = b) ∧
    -- and no entity instantiates itself
    (∀ a : W, ¬ iof a a) := by decide

end Model
end MLTStar
