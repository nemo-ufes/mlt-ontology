# MLT* in Lean 4

A machine-checked encoding of the multi-level theory MLT* in Lean 4, alongside
the Alloy and TPTP specifications in this repository.

Everything the TPTP fragment `tptp/mlt-star.p` states as a conjecture is proved
here, plus the stratification notions of `mlt_star.als` and an explicit finite
model that establishes consistency by kernel computation.

There are **no `sorry`s** and **no dependencies** — not even Mathlib. The proofs
use only Lean 4 core and its three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

## Building

```sh
cd lean
lake build
```

Lean 4.23.0 is pinned in `lean-toolchain`; `elan` will fetch it automatically.

## File map

| File | Contents |
| --- | --- |
| `MLTStar/Defs.lean` | The signature (`Domain`), all defined notions, and the axioms (`Extensional`, `Grounded`, `Constants`) |
| `MLTStar/Basic.lean` | Types/individuals partition the domain; order properties of specialization; grounding on individuals; subordination |
| `MLTStar/Powertype.lean` | The powertype theorems `t1`–`t5` and `powertypeNotFirstOrder` |
| `MLTStar/Constants.lean` | Consequences of `a13`–`a15`: the chain `cIndividual : cFot : cSot`, their uniqueness, and that they are Cardelli powertypes of one another |
| `MLTStar/AntiPatterns.lean` | The anti-pattern theorems `ap1`, `ap2`, `ap3` |
| `MLTStar/Stratification.lean` | Basic, ordered and orderless types; the universal type is orderless |
| `MLTStar/Model.lean` | A four-element model, hence consistency |

## How the encoding is organised

MLT* has a single primitive, instantiation. It is carried by a class:

```lean
class Domain (E : Type u) where
  iof : E → E → Prop
```

Everything the TPTP file states as a *definitional* axiom — `a2`, `a3`,
`a5`–`a8`, `a10`–`a12`, and the complete/disjoint categorization and
partitioning definitions — becomes a Lean `def`. Definitions are conservative,
so they cannot introduce inconsistency, and the corresponding TPTP
biconditionals hold by `Iff.rfl`. What remains as genuine assumptions is small
and is split into three classes, so that the hypotheses of each theorem record
exactly which axioms it uses:

* `Extensional E` — extensionality for types (`a9`);
* `Grounded E` — grounding on individuals (`a4`);
* `Constants E` — the three constants of `a13`–`a15` with their specifications.

TPTP axiom `a1` ("every element of the domain is an entity") is discharged by
the encoding: the domain *is* a type.

### `a4` without the auxiliary set theory

First-order logic cannot quantify over sets, so `tptp/mlt-star.p` builds an
auxiliary theory of sets of types (the `singleton`, `unions`, `setidentity`,
`membershiptyping` and `setsareindividuals` axioms) purely in order to state
`a4`. Lean can quantify over predicates, so that scaffolding disappears:

```lean
grounded : ∀ S : E → Prop, (∃ y, S y) → (∀ y, S y → IsType y) →
  ∃ y, S y ∧ ∃ z, iof z y ∧ ¬ S z
```

This ranges over *all* classes of types, where the TPTP version ranges only
over the finite non-empty sets that `singleton` and `unions` force to exist, so
it is strictly stronger. Stronger assumptions prove more, so every theorem
verified against the TPTP file still holds — and `MLTStar.Model` shows the
strengthened theory is still consistent.

The pay-off is `MLTStar.exists_individual_reachable`: descending along
instantiation from any type eventually reaches an individual. That is the
`typeWellFounded` fact of `mlt_star.als`, here *derived* rather than assumed.

Note that MLT* deliberately admits self-instantiation — the type of all entities
is one of its own instances — so `iof` is neither asserted nor provably
irreflexive. `grounded` is the weaker well-foundedness condition the theory
actually needs.

## Correspondence with `tptp/mlt-star.p`

| TPTP | Lean |
| --- | --- |
| `a1` | discharged by the encoding |
| `a2`, `a3` | `Individual`, `IsType` |
| `a4` | `Grounded.grounded` |
| `a5`, `a6` | `FirstOrderType`, `SecondOrderType` |
| `a7`, `a8` | `Specializes`, `ProperSpecializes` |
| `a9` | `Extensional.typeExtensionality` |
| `a10`, `a11` | `IsPowertypeOf`, `Categorizes` |
| `a12` | `IsSubordinateTo` (paper reading), `IsSubordinateTo.tptp` (TPTP reading) |
| `completeCategorizationDefinition` | `CompletelyCategorizes` |
| `disjointCategorizationDefinition` | `DisjointlyCategorizes` |
| `partitioningDefinition` | `Partitions` |
| `a13`–`a15` | `Constants` |
| `typesAndIndividualsPartitionEntity` | `typesAndIndividualsPartitionEntity` |
| `t1_basetypeUnique` … `t5` | `t1_basetypeUnique` … `t5` |
| `powertypeNotFirstOrder` | `powertypeNotFirstOrder` |
| `ap1`, `ap2`, `ap3` | `ap1`, `ap2`, `ap3` |
| `satisfiability` report | `Model.consistent` |
| set scaffolding (`singleton`, `unions`, …) | not needed |

## Consistency

`MLTStar/Model.lean` gives an explicit four-element model:

```
ind  :  cInd  :  cFot  :  cSot
```

(`a : b` reads "`a` is an instance of `b`"; these are the only instantiations.)
`W` is finite and every MLT* predicate on it is decidable, so the kernel checks
`typeExtensionality` and the three constant specifications by evaluation;
`grounded` quantifies over arbitrary classes and is proved by hand.

This is the smallest possible model. `Constants` alone forces an individual to
exist (`MLTStar.exists_individual`: if nothing were an individual, then nothing
would instantiate `cIndividual`, so `cIndividual` would itself be an
individual), and that individual forces the whole chain.

Where Alloy establishes consistency within a bounded scope and the TPTP report
relies on an external prover, this is checked by the Lean kernel.

## Notes for the maintainers

Three things surfaced while transcribing the specifications. None of them
affects the theorems; all three are recorded rather than silently resolved.

1. **Subordination is defined differently in the Alloy and TPTP files.**
   `mlt_star.als` and the ER 2017 paper say that every instance of `t₁` proper
   specializes *some* instance of `t₂`:

   ```alloy
   isSubordinateTo[t1,t2] iff (all t3 : iof.t1 | some (t3.properSpecializes & iof.t2))
   ```

   `tptp/mlt-star.p` says *every*:

   ```tptp
   ![T3,T4]:( (iof(T3,T1)&iof(T4,T2))=>properSpecializes(T3,T4))
   ```

   Both are encoded (`IsSubordinateTo` and `IsSubordinateTo.tptp`), and
   `isSubordinateTo_of_tptp` proves the TPTP reading implies the paper's — the
   existential witness comes for free from the fact that `t₂`, being a type, has
   an instance. The converse fails as soon as `t₂` has two instances that a
   single instance of `t₁` cannot both specialize. Since no conjecture in the
   TPTP file mentions subordination, nothing there depends on the choice; the
   paper's reading is taken as primary here.

2. **The comments on `t1_basetypeUnique` and `t2_powertypeUnique` are swapped**
   relative to the formulae they annotate. `t1`'s formula fixes the base type
   and shows the powertype unique; its comment says the opposite, and `t2` is
   the mirror image. The formulae are transcribed as written and the Lean
   doc-strings describe what is actually proved.

3. **`a4` is not needed for any conjecture in the TPTP file.** This is why
   `Extensional` and `Grounded` are separate classes: a theorem can only use an
   axiom it names in its hypotheses, so the statements themselves record the
   dependency. No theorem in `Powertype.lean` or `AntiPatterns.lean` takes
   `[Grounded E]`. Sharper still, `t3`, `t4`, `powertypeNotFirstOrder` and `ap1`
   assume nothing beyond the definitions, and `ap2`/`ap3` need only the constant
   `cSot`. `a4` earns its place elsewhere: it is what yields
   `exists_individual_reachable`, the counterpart of the `typeWellFounded` fact
   that `mlt_star.als` has to assume.

## Beyond the TPTP fragment

`MLTStar/Stratification.lean` adds the part of `mlt_star.als` that the TPTP
fragment omits, and that makes MLT* a *star* extension of basic MLT:

* `BasicType` — the type of all individuals, or the Cardelli powertype of a
  basic type. `mlt_star.als` writes this as a biconditional whose intended
  solution is the least fixed point; Lean states the least fixed point directly,
  as an inductive predicate.
* `OrderedType` — a specialization of a basic type. These are the types of basic
  MLT.
* `OrderlessType` — any other type.

The three constants of `a13`–`a15` turn out to be the first three basic types,
and the main result of the module is that a universal type — one having every
entity as an instance — is necessarily orderless (`IsUniversal.orderlessType`).
That is exactly the phenomenon MLT* was introduced to accommodate.

## References

1. Carvalho, V. A., Almeida, J. P. A.: *Toward a well-founded theory for
   multi-level conceptual modeling*. Software & Systems Modeling, 2016.
   <https://doi.org/10.1007/s10270-016-0538-9>
2. Almeida, J. P. A., Fonseca, C. M., Carvalho, V. A.: *A Comprehensive Formal
   Theory for Multi-level Conceptual Modeling*. ER 2017.
   <https://doi.org/10.1007/978-3-319-69904-2_2>
