module multilevelmodelling

sig Entity{
  iof: set Entity,
  specializes: set Entity,
  properSpecializes: set Entity,
  isSubordinateTo: set Entity,
  powertypeOf: set Entity,
  characterizes: set Entity,
  compCharacterizes: set Entity,
  disjCharacterizes: set Entity,
  partitions: set Entity
}

//----------------------------------------Basic types represented as singletons--------------------------------------------------------------
//Representing the basic type "Individual"
one sig Individual extends Entity{}

//Representing the basic type "1stOT"
one sig FOT extends Entity{}

//Representing the basic type "2ndOT"
one sig SOT extends Entity{}

//Representing the basic type "3rdOT"
one sig TOT extends Entity{}
//-----------------------------------------------------------------------------------------------------------------------------------------------


//-------------------------------------------------------------------- Axioms --------------------------------------------------------------------

//Axiom A1
//An entity is an instance of “Individual” iff it is not possibly related to another entity through instantiation.
fact individualDef{
	all x:Entity, i:Individual | ( i in x.iof iff no iof.x)
}

//Axiom A2
//An entity t is an instance first-order type ("FOT") iff all its instances are Individuals (i.e., instances of “Individual”)
fact firstOrderTypeDef{
	all t:Entity, f:FOT|  f in t.iof iff (all x:Entity, i:Individual| some iof.t and (t in x.iof implies i in x.iof)) 
}

//Axiom A3
//An entity t is an instance second-order type ("SOT") iff all its instances are first-order types (i.e., instances of “FOT”)
fact secondOrderTypeDef{
	all t:Entity, s:SOT|  s in t.iof iff (all t':Entity, f:FOT| some iof.t and (t in t'.iof implies f in t'.iof))
}

//Axiom A4
//An entity t is an instance third-order type ("TOT") iff all its instances are second-order types (i.e., instances of “SOT”)
fact thirdOrderTypeDef{
   all t:Entity, th:TOT|  th in t.iof iff (all t':Entity, s:SOT| some iof.t and (t in t'.iof implies s in t'.iof))
}


//Axiom A5
//Each entity in our domain of enquiry is necessarily an instance of “Individual”, “1stOT”, “2ndOT” or “3rdOT” 
//(except “3rdOT” whose type is outside the scope of the formaliza-tion).
fact completenessAxiom{
	all s:SOT, f:FOT, i:Individual, t:TOT, x:Entity| f in x.iof or i in x.iof or  s in x.iof or  t in x.iof or x=t
}

//Axiom A6
//“Individual”, “1stOT”, “2ndOT” and “3rdOT” have no instances in common (i.e., their extensions are disjoint).
fact disjointnessAxiom{
	all s:SOT, f:FOT, i:Individual, t:TOT| no x:Entity| (f in x.iof and i in x.iof) or (s in x.iof and i in x.iof) or (t in x.iof and i in x.iof) or (f in x.iof and s in x.iof) or (f in x.iof and t in x.iof) or (t in x.iof and s in x.iof)
}

//Axiom A7
//Two types are equal iff the set of all their possible instances is the same
fact typesEqualityDef{
	all x,y:Entity, i:Individual|  i not in y.iof and i not in x.iof implies (iof.x = iof.y iff x=y)
}


//Axioms A8
//Specialization Definition: t1 specializes t2 iff all instances of t1 are also instances of t2.
fact specializationDef{
    all t1,t2:Entity | t2 in t1.specializes iff all e:Entity, i:Individual | i not in t1.iof and i not in t2.iof and (t1 in e.iof implies t2 in e.iof)
}

//Axiom A9
//Proper Specialization Definition: t1 proper specializes t2 iff t1 specializes t2 and is different from it.
fact properSpecializationDef{
	all t1,t2:Entity |  t2 in t1.properSpecializes iff (t2 in t1.specializes and t1!=t2)
}

//Axiom A10
//Subordination Definition: t1 is subordinate to t2 iff every instance of t1 specializes an instance of t2.
fact subordinationDef{
	all t1,t2:Entity | t2 in t1.isSubordinateTo iff (all i:Individual| i not in t1.iof and (all t3:Entity | (t1 in t3.iof implies (some t4:Entity| t2 in t4.iof  and t4 in t3.properSpecializes))))

}


//Axioms A11
//Powertype Definition: iff a type t1 is power type of a type t2 all instances of t1 are specializations of t2 and all possible specializations of t2 are instances of t1.
fact powertypeOfDef{
	all t1,t2:Entity | t2 in t1.powertypeOf iff (all t3:Entity, i:Individual | i not in t1.iof and (t1 in t3.iof iff t2 in t3.specializes))
	
}

//Axioms A12
//Characterization Definition: a type t1 characterizes a type t2 iff all instances of t1 are properSpecializations of t2
fact characterizationDef{
	all t1,t2:Entity | t2 in t1.characterizes iff (all t3:Entity , i:Individual | i not in t1.iof and (t1 in t3.iof implies t2 in t3.properSpecializes))
}

//Axiom A13
//CompleteCharacterization Definition
fact completeCharacterizationDef{
	all t1,t2:Entity | t2 in t1.compCharacterizes iff (t2 in t1.characterizes and (all e:Entity | t2 in e.iof implies (some t3:Entity | t3 in e.iof and t1 in t3.iof)))
}

//Axiom A14
//Disjoint Characterization Definition
fact disjointCharacterizationDef{
    all t1,t2:Entity | t2 in t1.disjCharacterizes iff (t2 in t1.characterizes and (all e,t3,t4:Entity | (t1 in t3.iof and t1 in t4.iof and t3 in e.iof and t4 in e.iof) implies (t3=t4)))
	//The same definition using the lone quantifier
	//all t1,t2:Entity | t2 in t1.disjCharacterizes iff (t2 in t1.characterizes and (all e:Entity | t2 in e.iof implies (lone t3:Entity | t3 in e.iof and t1 in t3.iof)))
}

//Axiom A15
//Partitions Definition
fact partitionsDef{
	all t1,t2:Entity | t2 in t1.partitions iff (t2 in t1.disjCharacterizes and t2 in t1.compCharacterizes)
}

//------------------------------------------------------------------------Axioms Section End--------------------------------------------------

run {} for 18


//------------------------------------------------------------Theorems on Sosym paper------------------------------------------------------

//Theorems T1, T2 and T3
pred theoremsT1T2T3{
	//T1: “Individual” is an instance of “1stOT”
	all i:Individual, f:FOT | f in i.iof
	//T2: “1stOT” is an instance of “2ndOT”
	all f:FOT, s:SOT | s in f.iof
	//T3: “2ndOT” is an instance of “3rdOT”
	all t:TOT, s:SOT | t in s.iof
}

//Theorems T4, T5 and T6
//Any instance of a higher-order type (any instance of “1stOT”, “2ndOT”, and “3rdOT”) specializes the basic type at an order immediately lower order.
pred theoremsT4T5T6{
	//T4: Every instance of “1stOT” specializes “Individual”
	all t:Entity, i:Individual, f:FOT | f in t.iof iff i in t.specializes
	//T5: Every instance of “2ndOT” specializes “1stOT”
	all t:Entity, f:FOT, s:SOT | s in t.iof iff f in t.specializes
	//T6: Every instance of “3rdOT” specializes “2ndOT”
	all t:Entity, s:SOT, th:TOT | th in t.iof iff s in t.specializes
}

//Theorems T7, T8 and T9
pred theoremsT7T8T9{
	//T7: “1stOT” is powertype of “Individual”
	all i:Individual, f:FOT | i in f.powertypeOf
	//T8: “2ndOT” is powertype of “1stOT”
	all f:FOT, s:SOT | f in s.powertypeOf
	//T9: “3rdOT” is powertype of “2ndOT”
	all s:SOT, t:TOT | s in t.powertypeOf
}

//Theorem T10: each type has at most one power type 
pred theoremT10{
	all t:Entity| lone powertypeOf.t
}

//Theorem T11: each type is power type of, at most, one other type 
pred theoremT11{
	all t:Entity| lone t.powertypeOf
}

//Theorem T12: if a type t2 specializes a type t1 then the power type of t2 specializes the power type of t1.
//∀ t1,t2,t3,t4 (specializes(t2,t1)∧isPowertypeOf(t4,t2)∧isPowertypeOf(t3,t1))→specializes(t4,t3)
pred theoremT12{
	all t1,t2,t3,t4:Entity | (t1 in t2.specializes and t2 in t4.powertypeOf and t1 in t3.powertypeOf) implies t3 in t4.specializes
}

//Theorem T13: If a type t2 is power type of a type t1 and a type t3 characterizes the same base type t1 
//then all instances of t3 are also instances of the power type t2 and, thus, t3 proper specializes t2. 
//∀t1,t2,t3 (isPowertypeOf(t2,t1)∧characterizes(t3,t1))→properSpecializes(t3,t2)
pred theoremT13{
	all t1,t2,t3:Entity | (t1 in t2.powertypeOf and t1 in t3.characterizes) implies t2 in t3.properSpecializes
}


//Theorem T14: if two types t1 and t2 both partitions the same type t3 then it is not possible for t1 to specialize t2
//∀ t1,t2,t3,t4 (partitions(t1,t3)∧partitions(t2,t3))→¬properSpecializes(t1,t2)
pred theoremT14{
	all t1,t2,t3:Entity | (t3 in t1.partitions and t3 in t2.partitions) implies (t2 not in t1.properSpecializes)
}
//------------------------------------------------------------Theorems on Sosym paper - End --------------------------------------------------

assert allTheoremsOfSosymPaper{
	theoremsT1T2T3
	and theoremsT4T5T6
	and theoremsT7T8T9
	and theoremT10
	and theoremT11
	and theoremT12
	and theoremT13
	and theoremT14
}


//check allTheoremsOfSosymPaper for 18

//--------------------------------------------------Theorems not formally defined on Sosym paper--------------------------------------------------

//The theorems below are not explicity defined on Sosym paper but the rules that they formalize are cited in natural language

/*Since the instantiation relation denotes that an element is a member of the extension of a type,
 it must be irreflexive, asymmetric and intransitive */
assert iofProperties{
	//Assymetric
	all x,y:Entity | x in y.iof => y not in x.iof
	//Irreflexive
	all x:Entity | x not in x.iof
	//Intransitive
	all x,y,z:Entity | (y in x.iof and z in y.iof) => z not in x.iof
	//Acyclic
	all x:Entity | x not in x.^iof
}

/*Instantiation relations hold between two elements such that the last is one order higher than the former.*/
assert iofCrossLevel{
	all x,y:Entity, i:Individual, f:FOT, s:SOT, t:TOT | y in x.iof implies ((i in x.iof and f in y.iof) or (f in x.iof and s in y.iof) or (s in x.iof and t in y.iof) or (t in x.iof)) 
}

/*Specialization is a partial order relation (i.e., a reflexive, transitive and antisymmetric relation), which is guaranteed in this theory. */
assert specializationProperties{
	//Antissymetric
	all x,y:Entity | (x in y.specializes and x!=y) => y not in x.specializes
	//Reflexive
	all x:Entity, i:Individual | i not in x.iof => x  in x.specializes
	//Transitive
	all x,y,z:Entity | (y in x.specializes and z in y.specializes) => z  in x.specializes
}

/*Specializations and proper Specializations may only hold between types of the same order*/
assert specializationIntraLevel{
	all x,y:Entity, f:FOT, s:SOT, t:TOT | y in x.specializes implies ((f in x.iof and f in y.iof) or (s in x.iof and s in y.iof) or (t in x.iof and t in y.iof) or (t in x.specializes and t in y.specializes)) 
}

//subordination can only hold between higher-order types of equal order 
assert subordinationIntraLevel{
	all x,y:Entity, s:SOT, t:TOT | y in x.isSubordinateTo implies ((s in x.iof and s in y.iof) or (t in x.iof and t in y.iof) or (t in x.specializes and t in y.specializes)) 
}


//Given the power type definition (A11), if p1 is power type of t1 we conclude that p1 is one order higher then t1
assert powertypeOfCrossLevel{
	all x,y:Entity, f:FOT, s:SOT, t:TOT | x in y.powertypeOf implies ((f in x.iof and s in y.iof) or (s in x.iof and t in y.iof) or (t in x.iof and t in y.specializes)) 
}

//Characterization relations only occur between types of adjacent levels 
assert characterizationCrossLevel{
	all x,y:Entity, f:FOT, s:SOT, t:TOT | x in y.characterizes implies ((f in x.iof and s in y.iof) or (s in x.iof and t in y.iof) or (t in x.iof and t in y.specializes)) 
}

//The theorems below are not cited in Sosym paper, even in natural language

//If a type x characterizes a type y then x characterizes all supertypes of y
assert characterizationTransitivityThroughSpecialization{
	all x,y:Entity| y in x.characterizes implies all z:Entity | (z in y.specializes implies z in x.characterizes)
}

//Individual, FOT, SOT and TOT do not have supertypes
assert supertypesOfBasicTypes{
	all i:Individual, s:SOT, f:FOT, t:TOT | some i.specializes or some f.specializes or some s.specializes or some t.specializes
}
//-----------------------------------------------------------------------------------------------------------

//check characterizationCrossLevel for 18








