/**
*	MLT*
*	
*	MLT* extends basic MLT. The domain of quantification is a superset of Basic MLT, 
*	admiting types that are not stratified. This opens up the possibility of the types "Entity" 
*	(the type of all entities, i.e., the universe), "Type" (the type of all types), "OrderedType" 
*	(which is the type of all types in Basic MLT), etc.
*
*	Some known limitations of this specification are:
*		- Static classification only;
*		- No support for entity's features (attributes and domain relations).
*
*	Authors:
*		Victorio Carvalho - Basic MLT
*		João Paulo Almeida 	- Contributions to Basic MLT and initial developments of MLT*
*		Claudenir Fonseca - Revision and refactoring of MLT* and futher developments
*
*/

/**	GUIDE TO CLEAN THEME FOR VISUALIZATION
*
*	BLUE NODES	->	ORDERLESS TYPES
*	GREEN NODES	->	BASIC TYPES
*	GRAY NODES	->	ORDERED TYPES (specializations of Basic Types)
*	WHITE NODES	->	INDIVIDUALS
*
*	SIGNATURES AND SETS ARE NOT REPRESENTED BY LABELS.
*
*	'E' nodes stands for "Entity", e.g. "E1" stands for "Entity$1"
*
*	Direct instantiations and specializations are representented as edges.
*
*	Powertypes, direct characterizations and direct subordinations are represented
*	as attributes.
*	Disjoint characterization, complete characterizations and partitions ARE NOT
*	REPRESENTED BY DEFAULT, YOU NEED TO LOOK FOR THEM and make them
*	visible when necessary.
*
*	Model elements (Entity_, Type_, OrderedType_, OrderlessType_ and Individual_)
*	are represented by labels.
*/



module mltStar


/**					UTILS - PREDICATES AND FUNCTIONS				 	*/
/**	The predicates bellow are used throughout the code improving its readability.	*/


pred iof [ x,y:Entity ] 				{ x in iof.y }
pred specializes [ x,y:Entity ] 			{ x in specializes.y }
pred properSpecializes [ x,y:Entity ] 		{ x in properSpecializes.y }
pred powertypeOf [ x,y:Entity ] 			{ x in powertypeOf.y }
pred characterizes [ x,y:Entity ] 			{ x in characterizes.y }
pred compCharacterizes [ x,y:Entity ] 		{ x in compCharacterizes.y }
pred disjCharacterizes [ x,y:Entity ] 		{ x in disjCharacterizes.y }
pred partitions [ x,y:Entity ] 			{ x in partitions.y }
pred isSubordinateTo [ x,y:Entity ] 		{ x in isSubordinateTo.y }
pred disjointExtentions[t,t':Type] 		{ no iof.t & iof.t' }
pred disjoint_ [a, b :Entity] 			{ no a & b }


/**						MODEL SPECIFICATION							*/
/**						Signatures and Constraints						*/


/**	Entity
*	
*	Represents an entity, with all possible relations that may be established between 
*	entities according to the theory.
*/
sig Entity 
{ 
	iof: set Entity,
	directIof : set Entity
}

/**	Direct instantiations are used in order to simplify the visualization of instantiations. */
fact 
{
	all e :Entity | e.directIof = (e.iof) - (e.iof).properSpecializes 
}

/** 	Individual
*	
*	An individual is an entity that has no possible instances. The signature Individual
*	does not account for the entity Individual, which is going to be specified later throught
*	the signature Individual_ (with a underscore at the end).
*/
sig Individual in Entity {}
fact typeDef { all x:Entity | ( x in Individual iff no iof.x) }

/** 	Type
*	
*	A type is an entity that has instances. Also, types must be in an instantiation chain
*	that eventually leads to some individual. As Individual, Type does not account for 
*	the entity type, which is specified later as Type_.
*/
sig Type in Entity 
{
 	specializes: set Type,
	properSpecializes: set Type,
	isSubordinateTo: set Type,
	powertypeOf: set Type,
	characterizes: set Type,
	compCharacterizes: set Type,
	disjCharacterizes: set Type,
	partitions: set Type,

	directSpecializes : set Entity,
	isDirectSubordinateTo: set Type,
	directCharacterizes: set Type
}
fact 
{ 
	all e :Entity | ( e in Type iff some (iof.e))
}

/** Types are ultimately founded upon individuals */
fact typeWellFounded
{
	all t :Type | t in Type iff some (^iof.t & Individual)
}

/**	Direct relations are used in order to improve visualization of runs and checkings. */
fact 
{
	all t :Type | t.directSpecializes = (t.properSpecializes) - (t.properSpecializes).properSpecializes 
	all t :Type | t.isDirectSubordinateTo = (t.isSubordinateTo) - (t.isSubordinateTo).properSpecializes
	all t :Type | t.directCharacterizes = ((t.characterizes) - (t.characterizes+t.powertypeOf).properSpecializes)
}

/**	BasicType
*	
*	Basic types are the highest entities in their specialization chain of any instance order.
*	That is, for any given type order there is one entity that every ordered type 
*	specializes.
*	In other words, a basic type is a type at the top of the hierarchy of specializations
*	of types that are "stratified" in Basic MLT. */
sig BasicType in Type {}
fact
{
	all b :Type |  b in BasicType iff
		((all e :Entity | iof[e,b] iff e in Individual) 
		or 
		(some lot :BasicType | powertypeOf[b,lot]))
}

fact noIofLoopForBasicTypes
{
	all x:BasicType |  x not in x.^iof		// Not necessary in Basic MLT but saves up to 15 seconds
}

/**	OrderedType
*
*	A type is a ordered type iff it is a specialization of a basic type */
sig OrderedType in Type {}
fact
{
	all t :Type | t in OrderedType iff (some b:BasicType | specializes[t,b])
}

/**	OrderlessType
*	
*	A type is a orderless type iff it is not a ordered one. */
sig OrderlessType in Type {}
fact
{
	all t :Type | t in OrderlessType iff (no b:BasicType | specializes[t,b])
}



/**						CONSTANT MODEL ENTITIES						*/
/**		Signatures to reference the entities which instances are members 			*/
/** 							of the sets defined above						*/


-- Defining the "Individual_" basic type
sig Individual_ in Type {}
fact
{
	all e :Entity | e in Individual_ iff (all e' :Entity | iof[e',e] iff no iof.e')
}

--Defining the type "Type", whose instances are all types
sig Type_ in Entity {}
fact 
{
	all t :Entity | t in Type_ iff (all e :Entity | iof[e,t] iff e in Type)
}

--Defining the universal type "Entity"
sig Entity_ in Entity {}
fact
{
	all e :Entity | e in Entity_ iff (all e' :Entity | iof[e',e] iff e' in Entity)
}

--Defining the type "OrderedType", whose instances are all types
--whose instances are at the same order. These are the types in Basic MLT.
sig OrderedType_ in Entity {}
fact
{
	all e :Entity | e in OrderedType_ iff (all e' :Entity | iof[e',e] iff e' in OrderedType)
}

--Defining the type "OrderlessType", whose instances are all types
--whose instances spam through different orders. These are the types in Basic MLT.
sig OrderlessType_ in Entity {
}
fact {
	all e :Entity | e in OrderlessType_ iff (e in Type and (all e' :Entity | iof[e',e] iff e' in OrderlessType))
}



/** 								DEFINITIONS							*/



/** 	Axiom A7 - Two types are equal iff the set of all their possible instances is the 
*	same */
fact typesEquivalence
{
	all t1, t2 :Type | (t1 = t2 iff iof.t1 = iof.t2)
}

/** 	Axioms A8 - Specialization Definition: t1 specializes t2 iff all instances of t1 are also
*	instances of t2. */
fact specializationDefinition
{
	all t1, t2 :Type | specializes[t1,t2] iff (all e :iof.t1 | iof[e,t2])
}

/**	Axiom A9 - Proper Specialization Definition: t1 proper specializes t2 iff t1 specializes 
*	t2 and is different from it. */
fact properSpecializationDefinition 
{
	all t1, t2 :Type |  properSpecializes[t1,t2] iff (specializes[t1,t2] and t1!=t2)
}

/**	Axiom A10 - Subordination Definition: t1 is subordinate to t2 iff every instance of t1
*	specializes an instance of t2. */
fact subordinationDefinition 
{
	all t1, t2 :Type |
		isSubordinateTo[t1,t2] iff (all t3 :iof.t1 | some (t3.properSpecializes & iof.t2))
}

/**	Axioms A11 - Powertype Definition: iff a type t1 is power type of a type t2 all 
*	instances of t1 are specializations of t2 and all possible specializations of t2 are 
*	instances of t1. */
fact powertypeOfDefinition
{
	all pwt,t :Type | powertypeOf[pwt,t] iff (all t':Entity | (iof[t',pwt] iff specializes[t',t]))
}

/**	Axioms A12 - Categorization Definition: a type t1 characterizes a type t2 iff all 
*	instances of t1 are properSpecializations of t2. */
fact categorizationDefinition
{
	all t1, t2 :Type | characterizes[t1,t2] iff iof.t1 in properSpecializes.t2 // properSpecializes[iof.t1,t2]
}

/**	Axiom A13 - CompleteCharacterization Definition: a type t1 completely characterizes 
*	a type t2 iff t1 characterizes t2 and for every instance of t2 there is some type that
*	is instantiated by it and is instance of t1. */
fact completeCharacterizationDefinition
{
	all t1, t2 :Type |
		compCharacterizes[t1,t2] iff
		(characterizes[t1,t2] and (all e :iof.t2 | some e.iof & iof.t1))
		// Review the usage of "for all" without "implies"
}

/** Axiom A14 - Disjoint Characterization Definition: a type t1 completely characterizes 
*	a type t2 iff t1 characterizes t2 and there is for any pair of different types that are 
*	instances of t1 implies this pair have disjoint extensions. */
fact disjointCharacterizationDefinition
{
	all t1, t2 :Type | disjCharacterizes[t1,t2] iff
		(characterizes[t1,t2] and (all t3, t4 :iof.t1 | t3!=t4 implies disjoint_[iof.t3, iof.t4]))
}

/**	Axiom A15 - Partitions Definition: a type t1 partitions a type t2 iff t1 disjointly
*	characterizes t2 and t1 completely characterizes t2. */
fact partitionsDefinition
{
	all t1, t2 :Entity | partitions[t1,t2] iff (disjCharacterizes[t1,t2] and compCharacterizes[t1,t2])
}



/** 							USEFULL CONSTRAINTS						*/
/**				Some constraints for cutting out non-wanted models			*/



fact allEntitiesConnectedByInstantiation 
{
	let navigableiof = iof + ~iof | all x, y : Entity | (x in y.*navigableiof) 
}

fact someIndividuals
{
	some e : Entity | no iof.e 
}

fact someBasicTypes
{
	some BasicType
}



/** 							SIMULATIONS 								*/



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

run simulate2Level for 7
run simulate3Level for 10
run simulateMLTStar for 8
run simulateMLTStarPredefinedTypes for 15
