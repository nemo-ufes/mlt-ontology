/*
*		Multi-Level Theory Model
*		Version 2.1 (2015-04-01)
*
*		This version of MLT was designed to support dynamic classification
*
*/

module mlt_dynamicclassification

sig Entity{
	specializes: set Entity,
	properSpecializes: set Entity,
	isSubordinateTo: set Entity,
	powertypeOf: set Entity,
	characterizes: set Entity,
	compCharacterizes: set Entity,
	disjCharacterizes: set Entity,
	partitions: set Entity
}

some sig World{
   iof: set Entity -> Entity
} 


//---------------------------------------- Basic types declaration - Start --------------------------------------------------------------
/*
*		Once model types are unique entities/atoms they must be declared as singletons due Alloy's limitations
*/

//Representing the basic type "Individual"
one sig Individual extends Entity{}

//Representing the basic type "1stOT"
one sig FOT extends Entity{}

//Representing the basic type "2ndOT"
one sig SOT extends Entity{}

//---------------------------------------- Basic types declaration - End --------------------------------------------------------------

//----------------------------------------  MLT Axioms - Start --------------------------------------------------------------

/*
*		Axiom A1
*
*		An entity x is instance of Individual in a world w iff in any world x has no instances.
*/
pred A1_individualDef{
	all x:Entity, w1:World, i:Individual | (x in w1.iof.i) iff (all w2:World | no w2.iof.x)
}

/*
*		Axiom A2
*
*		An entity t is instance of FOT in a World w iff:
*			(i) exists some World w' where t has instances;
*			(ii) in any World, every iinstance of t is also instance of Individual.
*/
pred A2_firstOrderTypeDef{
	all t:Entity, w1:World, f:FOT| (t in (w1.iof).f) iff
		((some w2:World | some w2.iof.t) and 
		(all w3:World, x:Entity, i:Individual| x in (w3.iof).t implies x in (w3.iof).i))
}

/*
*		Axiom A3
*
*		An entity t is instance of SOT in a World w iff:
*			(i) exists some World w' which t has instances and;
*			(ii) in any World, every instance of t is also an instance of FOT.
*/
pred A3_secondOrderTypeDef{
	all t:Entity, w1:World, s:SOT | (t in (w1.iof).s) iff 
			((some w2:World | some w2.iof.t) and 
			(all w3:World, x:Entity, f:FOT| x in w3.iof.t implies x in w3.iof.f))
}

/*
*		Axiom A4
*
*		Each entity in our domain of enquiry is necessarily an instance of “Individual”, “1stOT” or “2ndOT”
*		(except “2ndOT” whose type is outside the scope of the formalization).
*
*/
pred A4_completenessAxiom{
	all s:SOT, f:FOT, i:Individual, x:Entity, w:World| 
		x in w.iof.i or x in w.iof.f or  x in w.iof.s or x=s
}


/*
*		Axiom A5
*
*		If t1 and t2 are types (which means they have instances), then they are equal iif their instances are
*		the same for every possible World.
*/
pred A5_typesEqualityDef{
	all t1,t2:Entity| 
		((some w1:World| some (w1.iof).t1) and (some w2:World| 
			some (w2.iof).t2)) implies (t1 = t2 iff (all w:World, x:Entity| x in w.iof.t1 iff x in w.iof.t2)) 
}

/*
*		Axioms A6
*		Specialization Definition
*		A type t specializes another type t’ iff in all possible worlds all instances of t are also instances of t’
*/
pred A6_specializationDef{
	all t1,t2:Entity | t2 in t1.specializes iff 
		(all e:Entity, i:Individual, w:World | 
			t1 not in w.iof.i and t2 not in w.iof.i and (e in w.iof.t1 implies e in w.iof.t2))
}

/*
*		Axiom A7
*
*		Proper Specialization Definition
*		t proper specializes t’ iff t specializes t’ and t is different from t’
*/
pred A7_properSpecializationDef{
	all t1,t2:Entity |  t2 in t1.properSpecializes iff (t2 in t1.specializes and t1!=t2)
}

/*
*		Axiom A8
*
*		Subordination Definition
*		t is subordinate to t’ iff every instance of t proper specializes an instance of t’.
*/
pred A8_subordinationDef{
	all t1,t2:Entity | t2 in t1.isSubordinateTo iff 
		(all i:Individual, w:World| t1 not in w.iof.i and 
			(all t3:Entity | (t3 in w.iof.t1 implies 
				(some t4:Entity| t4 in w.iof.t2  and t4 in t3.properSpecializes))))
}

/*
*		Axioms A9
*
*		Powertype Definition
*		a type t is power type of a base type t’ iff 
*		all instances of t specialize t’ and all possible specializations of t’ are instances of t.
*/
pred A9_powertypeOfDef{
	all t1,t2:Entity | t2 in t1.powertypeOf iff 
		(all t3:Entity, i:Individual, w:World | t1 not in w.iof.i and (t3 in w.iof.t1 iff t2 in t3.specializes))	
}

/*
*		Axioms A10
*
*		Characterization Definition
*		a type t characterizes a type t’ iff all instances of t are proper specializations of t’
*/
pred A10_characterizationDef{
	all t1,t2:Entity | t2 in t1.characterizes iff 
		(all t3:Entity , i:Individual, w:World | t1 not in w.iof.i and 
			(t3 in w.iof.t1 implies t2 in t3.properSpecializes))
}

/*
*		Axiom A11
*
*		CompleteCharacterization Definition
*		a type t completelyCharacterizes t’ iff t characterizes t’ and every instance of t’ is instance of, at least, an instance of t.
*/
pred A11_completeCharacterizationDef{
	all t1,t2:Entity | t2 in t1.compCharacterizes iff 
		(t2 in t1.characterizes and 	(all e:Entity, w:World |
			e in w.iof.t2 implies (some t3:Entity | e in w.iof.t3 and t3 in w.iof.t1)))
}

/*
*		Axiom A12
*
*		Disjoint Characterization Definition
*		t disjointlyCharacterizes t’	iff t characterizes t’ and every instance of t’ is instance of, at most, one instance of t.
*/
pred A12_disjointCharacterizationDef{
	all t1,t2:Entity | t2 in t1.disjCharacterizes iff 
		(t2 in t1.characterizes and (all e:Entity, w:World |
			e in (w.iof).t2 implies (lone t3:Entity |e in (w.iof).t3 and t3 in (w.iof).t1)))
}

/*
*		Axiom A13
*
*		Partitions Definition
*		t partitions t’ iff each instance of t is instance of exactly one instance of the base type t’
*/
pred A13_partitionsDef{
	all t1,t2:Entity | t2 in t1.partitions iff (t2 in t1.disjCharacterizes and t2 in t1.compCharacterizes)
}

fact {
	A1_individualDef
	A2_firstOrderTypeDef
	A3_secondOrderTypeDef
	A4_completenessAxiom
	A5_typesEqualityDef
	A6_specializationDef
	A7_properSpecializationDef
	A8_subordinationDef	
	A9_powertypeOfDef
	A10_characterizationDef
	A11_completeCharacterizationDef
	A12_disjointCharacterizationDef
	A13_partitionsDef
}
//----------------------------------------  MLT Axioms - End --------------------------------------------------------------


//----------------------------------------  MLT Theorems - Start -----------------------------------------------------------

//	Theorem T0
pred theoremT0{
// “Individual”, “1stOT” and “2ndOT” have no instances in common (i.e., their extensions are disjoint).
	all s:SOT, f:FOT, i:Individual, w:World| no x:Entity| 
		(x in (w.iof).i and x in (w.iof).f) or (x in (w.iof).i and x in (w.iof).s) 
		or (x in (w.iof).f and x in (w.iof).s) 
}


//		Theorems T1, T2 and T3
pred theoremsT1T2T3{
	//T1: “Individual” is an instance of “1stOT”
	all i:Individual, f:FOT, w:World| i in w.iof.f
	//T2: “1stOT” is an instance of “2ndOT”
	all f:FOT, s:SOT, w:World| f in w.iof.s
	//T3: “2ndOT” is an instance of “3rdOT”
	//all t:TOT, s:SOT , w:World| s in w.iof.t
}

//		Theorems T4, T5 and T6
//		Any instance of a higher-order type (any instance of “1stOT”, “2ndOT”, and “3rdOT”) 
//		specializes the basic type at an order immediately lower order.
pred theoremsT4T5T6{
	//T4: Every instance of “1stOT” specializes “Individual”
	all t:Entity, i:Individual, f:FOT, w:World | t in w.iof.f iff i in t.specializes
	//T5: Every instance of “2ndOT” specializes “1stOT”
	all t:Entity, f:FOT, s:SOT, w:World | t in w.iof.s iff f in t.specializes
	//T6: Every instance of “3rdOT” specializes “2ndOT”
	//all t:Entity, s:SOT, th:TOT, w:World | t in w.iof.th iff s in t.specializes
}

//		Theorems T7, T8 and T9
pred theoremsT7T8T9{
	//T7: “1stOT” is powertype of “Individual”
	all i:Individual, f:FOT | i in f.powertypeOf
	//T8: “2ndOT” is powertype of “1stOT”
	all f:FOT, s:SOT | f in s.powertypeOf
	//T9: “3rdOT” is powertype of “2ndOT”
	//all s:SOT, t:TOT | s in t.powertypeOf
}

//		Theorem T10: each type has at most one power type 
pred theoremT10{
	all t:Entity| lone powertypeOf.t
}

//		Theorem T11: each type is power type of, at most, one other type 
pred theoremT11{
	all t:Entity| lone t.powertypeOf
}

//		Theorem T12: if a type t2 specializes a type t1 then the power type of t2 specializes the power type of t1.
//		∀ t1,t2,t3,t4 (specializes(t2,t1)∧isPowertypeOf(t4,t2)∧isPowertypeOf(t3,t1))→specializes(t4,t3)
pred theoremT12{
	all t1,t2,t3,t4:Entity | (t1 in t2.specializes and t2 in t4.powertypeOf and t1 in t3.powertypeOf) implies t3 in t4.specializes
}

//		Theorem T13: If a type t2 is power type of a type t1 and a type t3 characterizes the same base type t1 
//		then all instances of t3 are also instances of the power type t2 and, thus, t3 proper specializes t2. 
//		∀t1,t2,t3 (isPowertypeOf(t2,t1)∧characterizes(t3,t1))→properSpecializes(t3,t2)
pred theoremT13{
	all t1,t2,t3:Entity | (t1 in t2.powertypeOf and t1 in t3.characterizes) implies t2 in t3.properSpecializes
}


//		Theorem T14: if two types t1 and t2 both partitions the same type t3 then it is not possible for t1 to specialize t2
//		∀ t1,t2,t3,t4 (partitions(t1,t3)∧partitions(t2,t3))→¬properSpecializes(t1,t2)
pred theoremT14{
	all t1,t2,t3:Entity | (t3 in t1.partitions and t3 in t2.partitions) implies (t2 not in t1.properSpecializes)
}


assert allTheoremsOfSosymPaper{
	theoremT0
	theoremsT1T2T3
	theoremsT4T5T6
	theoremsT7T8T9
	theoremT10
	theoremT11
	theoremT12
	theoremT13
	theoremT14
}

//check allTheoremsOfSosymPaper for 14 but exactly 2 World


//Definition of Rigidity
pred rigid[t:Entity] {
	some y:Entity | y in World.iof.t
	all w1,w2:World, x:Entity |	x in w1.iof.t implies x in w2.iof.t
}

//Proving that the basic types are rigid
pred baseTypesRigidity{all i:Individual, f:FOT, s:SOT| rigid[i] and rigid[f] and rigid[s] }


//Instances of FOT are not necessarily rigid - i.e., this assertion is not true
assert instancesOfFOTRigidityTest{
all f:FOT, x:Entity, w:World| x in (w.iof).f implies rigid[x]}

//check instancesOfFOTRigidityTest for 12 but 3 World

//----------------------------------------  MLT Theorems - End --------------------------------------------------------------


run {} for 10 but exactly 2 World
