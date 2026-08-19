# MLT* in Lean 4

A machine-checked encoding of the multi-level theory MLT* in Lean 4, alongside
the Alloy and TPTP specifications in this repository.

Everything the TPTP fragment `tptp/mlt-star.p` states as a conjecture is proved
here, plus the stratification notions of `mlt_star.als` and an explicit finite
model that establishes consistency by kernel computation.

There are **no `sorry`s** and **no dependencies** — not even Mathlib. The proofs
use only Lean 4 core and its three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

**[INSIGHTS.md](INSIGHTS.md)** collects what the encoding showed that was not
visible from the existing specifications — including that only five of the TPTP
file's 23 axioms survive as assumptions, that `a4` is used by no conjecture
there, and that `a13`–`a15` turns out to be the load-bearing one.

## Building

```sh
cd lean
lake build
```

Lean 4.23.0 is pinned in `lean-toolchain`; `elan` will fetch it automatically.

To audit which axioms each result actually rests on:

```sh
LEAN_PATH=.lake/build/lib/lean lean scripts/AxiomAudit.lean
```

## File map

| File | Contents |
| --- | --- |
| `MLTStar/Defs.lean` | The signature (`Domain`), all defined notions, and the axioms (`Extensional`, `Grounded`, `Constants`) |
| `MLTStar/Basic.lean` | Types/individuals partition the domain; order properties of specialization; grounding on individuals |
| `MLTStar/Powertype.lean` | The powertype theorems `t1`–`t5` and `powertypeNotFirstOrder` |
| `MLTStar/Constants.lean` | Consequences of `a13`–`a15`: the chain `cIndividual : cFot : cSot`, their uniqueness, and that they are Cardelli powertypes of one another |
| `MLTStar/AntiPatterns.lean` | The anti-pattern theorems `ap1`, `ap2`, `ap3` |
| `MLTStar/Orders.lean` | Order inheritance under specialization; powertypes raise the order; the constants are the tops of their orders |
| `MLTStar/Categorization.lean` | Characterisation of categorizers; a partition partitions; distinct partitions are incomparable |
| `MLTStar/Acyclicity.lean` | What `a4` rules out: no self-powertype, no self-categorizer |
| `MLTStar/Stratification.lean` | Basic, ordered and orderless types; the universal type is orderless |
| `MLTStar/Model.lean` | A four-element model, hence consistency |
| `INSIGHTS.md` | What the encoding showed that the Alloy and TPTP specifications did not |
| `scripts/AxiomAudit.lean` | Reports, per result, which axioms its proof term actually reaches |
| `derivation-graph.html` | The derivation graph drawn from that report |
| `Experiments/NoConstants.lean` | An alternative axiomatisation replacing `a13`–`a15`; see below |
| `Experiments/Designs.lean` | Specialization as a partial order, the powertype as an order embedding and right adjoint, independence of the axioms, and why comprehension is unavailable |
| `Experiments/Subordination.lean` | Why self-subordination is an ascending chain condition, and is refuted by finiteness rather than by order |
| `Experiments/Existence.lean` | What makes types exist: unions are not comprehension, meets fail for a different reason, and union closure forces orderless types |

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
| `a12` | `IsSubordinateTo` (per the paper and `mlt_star.als`; the TPTP formula was erroneous and has been corrected — see below) |
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

1. **`a12_subordinationDef` in `tptp/mlt-star.p` was wrong, and is now fixed.**
   It quantified universally where `mlt_star.als` and the ER 2017 paper quantify
   existentially — "every instance of `t₁` proper specializes *every* instance of
   `t₂`" instead of *some* instance:

   ```alloy
   isSubordinateTo[t1,t2] iff (all t3 : iof.t1 | some (t3.properSpecializes & iof.t2))
   ```
   ```tptp
   ![T3,T4]:( (iof(T3,T1)&iof(T4,T2))=>properSpecializes(T3,T4))
   ```

   The universal version collapses its second argument: any two instances of
   `t₂` would have to share an instance, so a `t₂` that disjointly categorizes
   anything could have at most one instance. `IsSubordinateTo` follows the paper
   and the Alloy specification, and the TPTP formula has been corrected to match.
   No conjecture in the TPTP file mentions subordination, so nothing proved there
   was affected.

2. **The formulae of `t1_basetypeUnique` and `t2_powertypeUnique` were
   interchanged** with respect to their names and comments: `t1`'s formula fixed
   the base type and showed the powertype unique, which is what its name and
   comment ascribe to `t2`. The two formulae have been swapped in the TPTP file
   so that each matches its name. Both were provable before and remain so — the
   Lean statements are unchanged — but each report in `tptp/reports` now
   corresponds to the other conjecture's formula.

3. **`a4` is not needed for any conjecture in the TPTP file.** This is why
   `Extensional` and `Grounded` are separate classes: a theorem can only use an
   axiom it names in its hypotheses, so the statements themselves record the
   dependency. `scripts/AxiomAudit.lean` turns that into a checkable count by
   walking the proof terms — of the 114 results, exactly **six** reach `a4`, and
   none of them is a TPTP conjecture:

   | Axiom | Results reaching it |
   | --- | --- |
   | none — definitions alone | 54 |
   | `a9` extensionality | 15 |
   | `a4` grounding | 6 |
   | `a13`–`a15` constants | 44 |

   Sharper still, `t3`, `t4`, `powertypeNotFirstOrder` and `ap1` assume nothing
   beyond the definitions, and `ap2`/`ap3` need only the constant `cSot`. `a4`
   earns its place elsewhere: it is what yields `exists_individual_reachable`,
   the counterpart of the `typeWellFounded` fact that `mlt_star.als` has to
   assume, and the acyclicity results of `Acyclicity.lean`.

## New theorems

Results proved here that neither `mlt_star.als` nor `tptp/mlt-star.p` states.

**Order structure** (`MLTStar/Orders.lean`)

* `IsPowertypeOf.secondOrderType` — the Cardelli powertype of a first-order type
  is a *second*-order type. Powertypes raise the order by exactly one.
  `powertypeNotFirstOrder` in the TPTP file is the special case that the
  powertype is not first-order.
* `firstOrderType_of_specializes`, `secondOrderType_of_specializes` — order is
  inherited downwards along specialization, hence
  `not_specializes_of_firstOrder_secondOrder` and its converse: specialization
  never crosses orders in either direction.
* `firstOrderType_iff_specializes_cIndividual` and the second-order analogue —
  being of order *n* is *the same thing as* specializing the *n*-th constant.
  `cIndividual` and `cFot` are the tops of their orders.
* `IsPowertypeOf.eq_cFot`, `IsPowertypeOf.eq_cSot` — `cFot` is *the* powertype of
  `cIndividual`, not merely one, and likewise for `cSot`.
* `FirstOrderType.not_iof_self`, `SecondOrderType.not_iof_self`.

**Categorization and partitioning** (`MLTStar/Categorization.lean`)

* `categorizes_iff` — the categorizers of `t` are *exactly* the specializations
  of the Cardelli powertype of `t` that do not have `t` itself as an instance.
  `t4` gives one half of one direction of this.
* `Partitions.existsUnique` — a partition really does partition: every instance
  of the base type instantiates exactly one instance of the partitioning type.
  The existing specifications state completeness and disjointness separately and
  never draw the conclusion the name promises.
* `Partitions.eq_of_specializes`, `Partitions.not_specializes` — distinct
  partitions of a type are specialization-incomparable.
* `IsPowertypeOf.not_categorizes` — a Cardelli powertype never categorizes its
  own base type.

**What `a4` rules out** (`MLTStar/Acyclicity.lean`)

`a4` is stated in the TPTP file but no conjecture there uses it, and
`mlt_star.als` assumes the corresponding `typeWellFounded` fact rather than
deriving anything from it. One lemma does the work:

* `not_all_instances_specialize` — no type has all of its instances specializing
  it. Such a type would be self-supporting: the class of its instances would be
  closed under instantiation, which is exactly what `a4` forbids.

Two shapes of circularity follow:

* `IsPowertypeOf.ne` — no type is its own Cardelli powertype;
* `not_categorizes_self`, `Categorizes.ne` — no type categorizes itself.

**The universal type** (`MLTStar/Stratification.lean`)

* `IsUniversal.unique` — there is at most one.
* `IsUniversal.not_firstOrderType`, `IsUniversal.not_secondOrderType` — it has no
  order at all, not merely "not the order of a basic type".

**Independence** (`MLTStar/Model.lean`)

* `no_universal`, `no_orderless` — the four-element model contains no universal
  type and no orderless type, so MLT* as axiomatised does not *entail* the star
  phenomena; it permits them. Showing this needs a model, which is why it
  appears in neither existing specification.

Note which of these need which axiom. `IsPowertypeOf.secondOrderType`,
`categorizes_iff` and `Partitions.existsUnique` assume nothing beyond the
definitions; the acyclicity results need only `a4`; the uniqueness results need
only `a9`.

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

## Experiments

`Experiments/` holds alternative axiomatisations, built as a separate Lake
library. `Experiments` imports `MLTStar`; nothing in `MLTStar` imports
`Experiments`, so the main development is unaffected by anything here.

### `NoConstants.lean` — replacing `a13`–`a15`

The audit makes the constants the load-bearing axiom, which invites the
question of what would have to replace them if we still wanted ordered types and
basic types as their topmost types. `Constants` turns out to bundle two
different jobs, and separating them is the whole answer:

* a **seed** — `Seeded`: a type of all individuals exists;
* a **successor** — `BasicPowertypeClosed`: every basic type has a Cardelli
  powertype.

What the file establishes:

| | |
| --- | --- |
| With neither | `Collapse` — a three-element model of `a9` and `a4` where no type has exactly the individuals as instances, so `BasicType` is empty and *every* type is orderless |
| `a4` alone | already forces an individual on any non-empty domain (`exists_individual_of_grounded`), so that much of `a13` was never needed |
| `Seeded` alone | recovers `cIndividual` as a *definition*, unique by `a9`, and gives order one |
| `Seeded` + closure | generates the tower `tower : Nat → E`, which is injective — so this axiomatisation forces an infinite domain |
| Together | they **prove** `Constants` (`constantsOfTower`), so everything in `MLTStar/` transfers |
| Strictness | the four-element model satisfies `Constants` but has no powertype for `cSot` (`Model.not_basicPowertypeClosed`), so the strengthening is real |
| Consistency | `Chain` — the natural numbers, each level the powertype of the one below, model all four axioms |

The trade is therefore precise: three primitive constants and a finite model, or
two existence axioms that generate every order and require an infinite one.

### Getting a finite model back

No *added* axiom can do it. Adding axioms removes models and never adds any, and
`Seeded` + `BasicPowertypeClosed` already prove `Nat` embeds in the domain
(`nat_embeds`), so every extension of that theory proves it too — including an
inconsistent one, which has no models at all. The successor axiom has to be
weakened rather than supplemented.

Bounding its height is the natural weakening. `Stratified D h` asks for a tower
that climbs `h` times and no further, so finite models are permitted again — and
it is not a new axiom: `Stratified D 2` and `Constants D` prove each other
(`constantsOfStratified`, `stratified_of_constants`). `a13`–`a15` *is* bounded
closure at height two, written out as three constants rather than as a schema,
which is why the four-element model satisfies it (`Model.stratified_two`).

### `Designs.lean` — alternative shapes for the theory

* **Specialization is a partial order on the types**, not on the entities: on the
  full domain it is not reflexive, since an individual specializes nothing.
* **The powertype is an order embedding**: `t3` says it preserves specialization,
  and `specializes_powertype_iff` shows it reflects it too. `t2` then falls out
  as injectivity. This suggests presenting MLT* as *a poset of types with a
  bottom and an injective, fixed-point-free order embedding*, with the orders and
  basic types derived from its orbit.
* **The axioms are independent**: `extensional_independent` and
  `grounded_independent` give models satisfying all but `a9`, and all but `a4`,
  respectively. With `Collapse` in `NoConstants.lean`, all three are pairwise
  independent.
* **Comprehension is unavailable**: `no_comprehension` is Russell's argument on
  instantiation, and `no_separation_with_universal` shows the usual repair fails
  once a universal type exists — which is what MLT* was extended to admit. This
  does *not* rule out bounded type-forming operations; see `Existence.lean`.

* **The powertype is a right adjoint**, to "union of instances":
  `union_powertype` shows union inverts `℘` on its image, and
  `union_specializes_iff` is the adjunction law `L p ⊑ t ↔ p ⊑ ℘ t` for arbitrary
  `p` and `t`. Neither needs an axiom. MLT* does not look like it has an
  adjunction only because it cannot guarantee the unions exist.

### `Subordination.lean` — where irreflexivity comes from

Self-subordination unfolds to "the instances of `t` have no maximal element under
proper specialization", so irreflexivity is an *ascending* chain condition. `a4`
constrains instantiation *descending*, and orderedness says nothing about
ascending chains, so neither helps. What does is finiteness:
`nat_embeds_of_self_subordinate` shows a self-subordinate type embeds `Nat` into
its own instances, so subordination is irreflexive in every finite model.

### `Existence.lean` — what makes types exist

The base theory says almost nothing about which types there are. `IsPowertypeOf`
is a defined relation, never asserted to be inhabited, so the only types MLT*
claims outright are the three constants; everything else is conditional.

* **Union is not comprehension.** A binary union is bounded and does not
  reproduce Russell. Adding it makes the types a join-semilattice
  (`IsJoinOf.least` shows the union really is the least upper bound), and
  `Pair.consistent` gives a model.
* **Meets fail for a different reason entirely.** `Individual` is *defined* as
  "has no instances", so there is no empty type (`no_empty_type`), and disjoint
  types have no meet (`no_meet_of_disjoint`). This bites exactly where MLT*'s own
  partitioning applies (`no_meet_of_disjointlyCategorizes`).
* **Union closure forces orderless types.** `exists_orderlessType`: with the
  constants and binary unions, the union of `cIndividual` and `cFot` has both an
  individual and a type among its instances, and `not_orderedType_of_mixed` makes
  anything mixed orderless. Where `Model.no_orderless` shows the base axioms
  merely permit the star phenomena, one bounded existence principle forces them.

See `INSIGHTS.md` §9–13 for the discussion and the remaining open targets.
