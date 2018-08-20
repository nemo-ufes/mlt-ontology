module mltStarValidation

open mlt_star


/**					UTILS - PREDICATES AND FUNCTIONS				 	*/
/**	The predicates bellow are used throughout the code improving its readability.	*/


pred triviallyCharacterizes[t,t':Type]
{
	characterizes[t,t'] and (some t" :Type | 
		(characterizes[t,t"] or powertypeOf[t,t"]) and properSpecializes[t",t'])
}

pred triviallySubordinateTo[t,t':Type]
{
	isSubordinateTo[t,t'] and (some t" :Type | 
		isSubordinateTo[t,t"] and properSpecializes[t",t'])
}


/**						THEOREMS FROM SOSYM PAPER					*/



/** Theorem T10: each type has at most one power type */
pred theoremT10
{
	all t:Entity| lone powertypeOf.t
}

/** Theorem T11: each type is power type of, at most, one other type */
pred theoremT11
{
	all t:Entity| lone t.powertypeOf
}

/**	Theorem T12: if a type t2 specializes a type t1 then the power type of t2 specializes 
*	the power type of t1.
*
*	∀ t1,t2,t3,t4 (specializes(t2,t1)∧isPowertypeOf(t4,t2)∧isPowertypeOf(t3,t1))
*		→specializes(t4,t3) 
*/
pred theoremT12
{
	all t1,t2,t3,t4:Entity | (t1 in t2.specializes and t2 in t4.powertypeOf and t1 in t3.powertypeOf) implies t3 in t4.specializes
}

/**	Theorem T13: If a type t2 is power type of a type t1 and a type t3 characterizes the 
*	same base type t1 then all instances of t3 are also instances of the power type t2 
*	and, thus, t3 proper specializes t2. 
*
*	∀t1,t2,t3 (isPowertypeOf(t2,t1)∧characterizes(t3,t1))→properSpecializes(t3,t2) 
*/
pred theoremT13
{
	all t1,t2,t3:Entity | (t1 in t2.powertypeOf and t1 in t3.characterizes) implies t2 in t3.properSpecializes
}


/**	Theorem T14: if two types t1 and t2 both partitions the same type t3 then it is not 
*	possible for t1 to specialize t2.
*	
*	∀ t1,t2,t3,t4 (partitions(t1,t3)∧partitions(t2,t3))→¬properSpecializes(t1,t2) 
*/
pred theoremT14
{
	all t1,t2,t3:Entity | (t3 in t1.partitions and t3 in t2.partitions) implies (t2 not in t1.properSpecializes)
}



/**						THEOREMS - NON FORMALIZED (SOSYM)			*/
/**	The theorems below are not explicity defined on Sosym paper but the rules that 
*	they formalize are cited in natural language*/



/**	Since the instantiation relation denotes that an element is a member of the extension 
*	of a type, it must be irreflexive, asymmetric and intransitive */
pred iofProperties
{
	all x,y:Entity | x in y.iof => y not in x.iof					/** Assymetric */
	all x:Entity | x not in x.iof								/** Irreflexive */
	all x,y,z:Entity | (y in x.iof and z in y.iof) => z not in x.iof		/** Intransitive */
	all x:Entity | x not in x.^iof							/** Acyclic */
}

/**	The instantiation properties specified on Sosym's paper are only aplicable to 
*	Basic MLT, so the following predicated was corrected in this sense. */
pred iofPropertiesForOrderedTypes
{
	all x,y :OrderedType+Individual  | iof[y,x] implies y not in x.iof	/** Assymetric */
	all x :OrderedType+Individual | not iof[x,x]					/** Irreflexive */
	all x,y,z :OrderedType+Individual | 
		(iof[x,y] and iof[y,z]) implies not iof[x,z]				/** Intransitive */
	all x :OrderedType+Individual | x not in x.^iof				/** Acyclic */
}

/**	Specialization is a partial order relation (i.e., a reflexive, transitive and antisymmetric 
*	relation), which is guaranteed in this theory for ordered types. */
pred specializationProperties
{
	all disj x, y :Entity | specializes[y,x] => not specializes[x,y]		/** Antissymetric */
	all t :Type | specializes[t,t]								/** Reflexive */
	all x, y, z :Entity | 
		(specializes[x,y] and specializes[y,z]) implies specializes[x,z]	/** Transitive */
}

/** This "theorem" is to check the structure of Basic Types present in old good MLT. */
pred basicMLTPattern 
{
	// all types specialize a basic type y and instantiate z such that
	// z is the basic type immediately higher than y (except at the top)
	all x:OrderedType | some y: BasicType | 
		(specializes[x,y]) and
		((no b : BasicType | iof[y,b]) or // basic type is at the top of basic types
		(some z: BasicType | iof[y,z] and iof[x,z] )) // or type is instance of basic type at higher order
}

pred subordinationProperties
{
	no t, t' :Type | 
		isSubordinateTo[t,t'] and isSubordinateTo[t',t]	/** Irreflexive and Asymmetric*/
	all t, t', t" :Type | (isSubordinateTo[t,t'] and specializes[t',t"]) 
		implies isSubordinateTo[t,t"]						/** Transitive */
}



/**							NEW THEOREMS							*/
/**	The theorems below are not cited in Sosym paper, even in natural language 		*/



/** 	Since every specialization of Entity_ has instances, it has is and instance of Type_. 
*	Also, every instance of Type_ is a specialization of Entity_. So, Type_ is powertype of
*	Entity. */
pred TypeIsPowerTypeOfEntity
{
	all t :Type_, e :Entity_ | powertypeOf[t,e]
}

/**	This "theorem" shows the basic model of MLT*, the same MLT Basic Types does. */
pred mltStarPattern
{
	all t :Type_, e :Entity_ | iof[t,e]
	all t :Type_, e :Entity_ | iof[e,t]
	lone Entity_ 
	lone Type_ 
	lone OrderlessType_ 
	lone OrderedType_ 
	lone Individual_ 
}

/**	If a type t has some cross-level relation to some type t', t is going to characterize
*	every type t' specializes from. */
pred trivialCharacterization
{
	all t, t' :Type | 
		(powertypeOf[t,t'] or characterizes[t,t']) implies 
		(all t" :Type | properSpecializes[t',t"] implies characterizes[t,t"])
}

/**	A type can only be a powertype or characterizer of other type, excluding trivial 
*	characterizations. */
pred uniqueCrossLevelRelation
{
	all disj t, t', t" :Type | 
		(characterizes[t,t'] and powertypeOf[t,t"]) implies triviallyCharacterizes[t,t']
}

/**	Every type that is source of a cross-level relation characterizes Entity_, unless
*	it is the the powertype of Entity_, Type_. */
pred allCharacterizesOfEntity_
{
	let sources = (powertypeOf + characterizes).Type | all t :sources | 
		some Entity_ implies (characterizes[t,Entity_] or t in Type_)
}

pred noSelfCharacterization 
{ 
	no t :OrderedType | t in characterizes.Type and iof[t,t] 
}

pred noMultilpleCharacterizationOfOrderedTypes
{
	/** I'd like to expand this to all types */
	all disj t, t', t" :OrderedType | 
		(characterizes[t,t'] and characterizes[t,t"] and properSpecializes[t',t"]) implies
			(triviallyCharacterizes[t,t"])
}

/**	This is not a new theorem, it is the transitivity the paper describes on the table*/
pred trivialSubordination
{
	all t, t' :Type | isSubordinateTo[t,t'] implies isSubordinateTo[t,t'.specializes]
}

pred inheritedCharacterization
{
	all t, t' :Type | 
		(characterizes[t,t'] and not triviallyCharacterizes[t,t']) implies 
			(all t" :Type | specializes[t",t] implies characterizes[t",t'])
}

/** Reflexive, assymetric, transitive */
pred specializesProperties
{
	all t :Type | specializes[t,t]
	no t, t' :Type | specializes[t,t'] and specializes[t',t]
	all t, t', t'' :Type | specializes[t,t'] and specializes[t',t''] implies specializes[t,t'']
}

/** Irreflexive, assymetric, transitive */
pred properSpecializesProperties
{
	no t :Type | properSpecializes[t,t]
	no t, t' :Type | properSpecializes[t,t'] and properSpecializes[t',t]
	all t, t', t'' :Type | properSpecializes[t,t'] and properSpecializes[t',t''] implies properSpecializes[t,t'']
}

/** Irreflexive */
pred isSubordinateToProperties
{
	no t :Type | isSubordinateTo[t,t]
	// TIMEOUT - no t, t' :Type | isSubordinateTo[t,t'] and isSubordinateTo[t',t]
	// TIMEOUT - all t, t', t'' :Type | isSubordinateTo[t,t'] and isSubordinateTo[t',t''] implies isSubordinateTo[t,t'']
}

/** Irreflexive, assymetric, intransitive */
pred powertypeOfProperties
{
	no t :Type | powertypeOf[t,t]
	no t, t' :Type | powertypeOf[t,t'] and powertypeOf[t',t]
	no t, t', t'' :Type | powertypeOf[t,t'] and powertypeOf[t',t''] and powertypeOf[t,t'']
}

/** Irreflexive, assymetric, non-transitive */
pred characterizesProperties
{
	no t :Type | characterizes[t,t]
	no t, t' :Type | characterizes[t,t'] and characterizes[t',t]
	no t, t', t'' :Type | characterizes[t,t'] and characterizes[t',t''] and characterizes[t,t'']
}

/** Irreflexive, assymetric, intransitive */
pred compCharacterizesProperties
{
	no t :Type | compCharacterizes[t,t]
	no t, t' :Type | compCharacterizes[t,t'] and compCharacterizes[t',t]
	no t, t', t'' :Type | compCharacterizes[t,t'] and compCharacterizes[t',t''] and compCharacterizes[t,t'']
}

check { compCharacterizesProperties } for 11

/** Irreflexive, assymetric, non-transitive */
pred disjCharacterizesProperties
{
	no t :Type | disjCharacterizes[t,t]
	no t, t' :Type | disjCharacterizes[t,t'] and disjCharacterizes[t',t]
	//no t, t', t'' :Type | disjCharacterizes[t,t'] and disjCharacterizes[t',t''] and disjCharacterizes[t,t'']
}

/** Irreflexive, assymetric, intransitive */
pred partitionsProperties
{
	no t :Type | partitions[t,t]
	no t, t' :Type | partitions[t,t'] and partitions[t',t]
	no t, t', t'' :Type | partitions[t,t'] and partitions[t',t''] and partitions[t,t'']
}

check
{
	// no t :OrderlessType, t':OrderedType | characterizes[t,t']
	//Type = OrderedType+OrderlessType
	no e :Entity | #(e.iof & BasicType) > 1
}
for 10

-- Defining the "R_" basic type
sig R_ in Type {}
fact {
	all e : Entity |
	e in R_ iff
	(
	(all x : Entity | e in x.iof iff (x not in iof.x))
	)
}

-- existence of the  "Russellian" type
pred noRussellProperty
{
	no R_   
} 



/** 							SIMULATIONS HELPERS						*/



pred simulate2Level
{
	// simulates two-level model (non multi-level)
	#BasicType=1 and no OrderlessType
}

pred simulate3Level
{
	// simulates three-level model (multi-level but no OrderlessType)
	#BasicType=2 and no OrderlessType
}

pred simulateMLTStar
{ 
	// simulates three-level model with orderless entities
	#BasicType=3 and some OrderlessType
}

pred simulateMLTStarPredefinedTypes -- MLT star with all the predefined types
{
	some Entity_ and some Type_ and some OrderedType_ and some OrderlessType_
		and some BasicType
	some OrderedType - BasicType
} 

assert formalizedSosymTheorems
{
	BasicType in OrderedType
	theoremT10 and theoremT11 and theoremT12 and theoremT13 and theoremT14
}

assert nonFormalizedSosymTheorems
{
	iofPropertiesForOrderedTypes
	specializationProperties
	basicMLTPattern
	subordinationProperties
}

assert newTheorems
{
	TypeIsPowerTypeOfEntity
	mltStarPattern
	trivialCharacterization 
	uniqueCrossLevelRelation
	allCharacterizesOfEntity_ 
	noSelfCharacterization
	noMultilpleCharacterizationOfOrderedTypes
	trivialSubordination
	inheritedCharacterization
}

assert allTheorems
{
	/** formalizedSosymTheorems */
	BasicType in OrderedType
	theoremT10 and theoremT11 and theoremT12 and theoremT13 and theoremT14
	/** nonFormalizedSosymTheorems */
	iofPropertiesForOrderedTypes
	specializationProperties
	basicMLTPattern
	subordinationProperties
	/** newTheorems */
	TypeIsPowerTypeOfEntity
	mltStarPattern
	trivialCharacterization 
	uniqueCrossLevelRelation 
	allCharacterizesOfEntity_ 
	noSelfCharacterization
	noMultilpleCharacterizationOfOrderedTypes
	trivialSubordination
	inheritedCharacterization
}

assert noRussellProperty_ {
	noRussellProperty
}





/** 							SIMULATIONS								*/





run simulate2Level for 7
run simulate3Level for 10
run simulateMLTStar for 8
run simulateMLTStarPredefinedTypes for 15

check formalizedSosymTheorems for 7
check nonFormalizedSosymTheorems for 7
check newTheorems for 11
check allTheorems for 7
check noRussellProperty_ for 8

/* It is necessary at least 7 entities in order to instantiated MLT* basic model. */
